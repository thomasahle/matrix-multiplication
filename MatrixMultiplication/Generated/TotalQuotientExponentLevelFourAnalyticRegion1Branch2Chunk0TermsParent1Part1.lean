import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 0, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 41246823021144514488681229189120
def positiveArguments : Array ℕ := #[
    11, 3, 1, 1, 1, 1,
    37509, 3932751, 42391125, 1966377, 37509, 170685,
    8363331, 35, 31, 1451, 395, 4181667,
    1451, 35, 35, 15, 35, 395,
    15, 85341, 31, 1538059, 501, 8675317,
    807, 25, 807, 539, 1542155, 501,
    3, 535, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    871509787656907713528983453696, 475368975085586025561263702016, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584, 19807040628566084398385987584,
    354262488811915044641046528, 37143783015744160167616315392, 400372855742274977918877696000, 37143811349943057385487597568, 354262488811915044641046528, 1612074246257210786599403520,
    78989427999089345549410762752, 676998458984192337835458560, 599627206528856070654263296, 28066421828173230919978582016, 7640411179964456384143032320, 78989456333288242767282044928,
    28066421828173230919978582016, 676998458984192337835458560, 676998458984192337835458560, 580284393415022003858964480, 676998458984192337835458560, 7640411179964456384143032320,
    580284393415022003858964480, 1612045912058313568728121344, 599627206528856070654263296, 14526556540552007295464112128, 19381498740061734928889413632, 163872104916276967625382166528,
    31219300365728183807612289024, 967140655691703339764940800, 31219300365728183807612289024, 20851552536713124005332123648, 14565242166779675429054709760, 19381498740061734928889413632,
    928455029464035206174343168, 41393620063604902941939466240, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    3, 1, 0, 0, 0, 0,
    15, 21, 25, 20, 15, 17,
    22, 5, 4, 10, 8, 21,
    10, 5, 5, 3, 5, 8,
    3, 16, 4, 20, 8, 23,
    9, 4, 9, 9, 20, 8,
    1, 9, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    26483035, 4306977, 20858847, 4306977, 48413445, 4053615867,
    2026808667, 24205989, 37509, 3932751, 42391125, 1966377,
    37509, 3, 1, 3, 3, 1,
    1
  ]
def negativeCoefficients : Array ℕ := #[
    122131442235023158820208640, 39724851225176671745212416, 384777812281664259596746752, 39724851225176671745212416, 111633803705201665391984640, 9347001808959656997509136384,
    9347005191631351513998163968, 111630421033507148902957056, 177131244405957522320523264, 18571891507872080083808157696, 200186427871137488959438848000, 18571905674971528692743798784,
    177131244405957522320523264, 475368975085586025561263702016, 79228162514264337593543950336, 475368975085586025561263702016, 237684487542793012780631851008, 316912650057057350374175801344,
    158456325028528675187087900672
  ]
def negativeScales : Array ℕ := #[
    24, 22, 24, 22, 25, 31,
    30, 24, 15, 21, 25, 20,
    15, 1, 0, 1, 1, 0,
    0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    3459431618637292, 1584962500720924, 0, 0, 0, 0,
    15194949180424810, 21907107414734823, 25337258918181433, 20907108515257955, 15194949180424810, 17380976752623911,
    22995646230370185, 5129283016944966, 4954196309696329, 10502831804066725, 8625708843063759, 21995646747877414,
    10502831804066725, 5129283016944966, 5129283016944966, 3906890595303263, 5129283016944966, 8625708843063759,
    3906890595303263, 16380951395251214, 4954196309696329, 20552679415520317, 8968666792316714, 23048485044706399,
    9656424863276222, 4643856189773592, 9656424863276222, 9074141462752505, 20556516345272997, 8968666792316714,
    1584962500720924, 9063395081288509, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    24658565131116628, 22038244188684178, 24314156077421308, 22038244188684178, 25528904421240604, 31916562240947312,
    30916562763057331, 24528860704754590, 15194949180424811, 21907107419999676, 25337258918181435, 20907108520522911,
    15194949180424811, 1584962500724866, 0, 1584962500724866, 1584962500724866, 0,
    0
  ]

abbrev PositiveTerm := Fin 41
abbrev NegativeTerm := Fin 19
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
noncomputable def positiveFloor : ℝ := 80692947 / 250000000000
noncomputable def negativeCeiling : ℝ := 100669709 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 122131442235023158820208640, coefficient := (-122131442235023158820208640) }, { argument := 39724851225176671745212416, coefficient := (-39724851225176671745212416) }, { argument := 384777812281664259596746752, coefficient := (-384777812281664259596746752) }, { argument := 39724851225176671745212416, coefficient := (-39724851225176671745212416) }, { argument := 111633803705201665391984640, coefficient := (-111633803705201665391984640) }, { argument := 9347001808959656997509136384, coefficient := (-9347001808959656997509136384) }, { argument := 9347005191631351513998163968, coefficient := (-9347005191631351513998163968) }, { argument := 111630421033507148902957056, coefficient := (-111630421033507148902957056) }, { argument := 177131244405957522320523264, coefficient := (-177131244405957522320523264) }, { argument := 18571891507872080083808157696, coefficient := (-18571891507872080083808157696) }, { argument := 200186427871137488959438848000, coefficient := (-200186427871137488959438848000) }, { argument := 18571905674971528692743798784, coefficient := (-18571905674971528692743798784) }, { argument := 177131244405957522320523264, coefficient := (-177131244405957522320523264) }, { argument := 871509787656907713528983453696, coefficient := 871509787656907713528983453696 }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 19807040628566084398385987584, coefficient := 19807040628566084398385987584 }, { argument := 79228162514264337593543950336, coefficient := (-79228162514264337593543950336) }, { argument := 354262488811915044641046528, coefficient := 354262488811915044641046528 }, { argument := 37143783015744160167616315392, coefficient := 37143783015744160167616315392 }, { argument := 400372855742274977918877696000, coefficient := 400372855742274977918877696000 }, { argument := 37143811349943057385487597568, coefficient := 37143811349943057385487597568 }, { argument := 354262488811915044641046528, coefficient := 354262488811915044641046528 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1612074246257210786599403520, coefficient := 1612074246257210786599403520 }, { argument := 78989427999089345549410762752, coefficient := 78989427999089345549410762752 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 28066421828173230919978582016, coefficient := 28066421828173230919978582016 }, { argument := 7640411179964456384143032320, coefficient := 7640411179964456384143032320 }, { argument := 78989456333288242767282044928, coefficient := 78989456333288242767282044928 }, { argument := 28066421828173230919978582016, coefficient := 28066421828173230919978582016 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 580284393415022003858964480, coefficient := 580284393415022003858964480 }, { argument := 676998458984192337835458560, coefficient := 676998458984192337835458560 }, { argument := 7640411179964456384143032320, coefficient := 7640411179964456384143032320 }, { argument := 580284393415022003858964480, coefficient := 580284393415022003858964480 }, { argument := 1612045912058313568728121344, coefficient := 1612045912058313568728121344 }, { argument := 599627206528856070654263296, coefficient := 599627206528856070654263296 }, { argument := 237684487542793012780631851008, coefficient := (-237684487542793012780631851008) }, { argument := 14526556540552007295464112128, coefficient := 14526556540552007295464112128 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 163872104916276967625382166528, coefficient := 163872104916276967625382166528 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 967140655691703339764940800, coefficient := 967140655691703339764940800 }, { argument := 31219300365728183807612289024, coefficient := 31219300365728183807612289024 }, { argument := 20851552536713124005332123648, coefficient := 20851552536713124005332123648 }, { argument := 14565242166779675429054709760, coefficient := 14565242166779675429054709760 }, { argument := 19381498740061734928889413632, coefficient := 19381498740061734928889413632 }, { argument := 928455029464035206174343168, coefficient := 928455029464035206174343168 }, { argument := 316912650057057350374175801344, coefficient := (-316912650057057350374175801344) }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk0
