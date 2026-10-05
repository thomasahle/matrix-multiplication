import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-92795601218806010796187826153062400)
def positiveArguments : Array ℕ := #[
    611, 39, 93, 285, 843, 1881,
    93, 939, 1911, 93, 285, 93,
    3, 9, 19, 49, 41, 1147,
    35, 41, 37, 19, 19, 37,
    1147, 37, 3, 49, 3, 1335885567,
    1335886081, 33819795873, 122929804001, 16911398335, 2974446285, 117548865943,
    117548872549, 2974466103, 28770103, 643307029, 106520718029, 10292918023,
    28770103, 9393401, 1844488967, 230561123, 1174173
  ]
def positiveCoefficients : Array ℕ := #[
    378190682001683673981682450432, 386237292257038645768526757888, 3597763239173136423925579776, 88203227799083344586562600960, 65223965819848473233747607552, 72767662934243759283914145792,
    3597763239173136423925579776, 72651606055560754883142352896, 73928231721073803291632074752, 3597763239173136423925579776, 88203227799083344586562600960, 3597763239173136423925579776,
    1856910058928070412348686336, 1392682544196052809261514752, 1470053796651389076442710016, 1895595685155738545939283968, 25377770805350295635432046592, 44372413283135349228415483904,
    1353996917968384675670917120, 25377770805350295635432046592, 1431368170423720942852112384, 1470053796651389076442710016, 1470053796651389076442710016, 1431368170423720942852112384,
    44372413283135349228415483904, 1431368170423720942852112384, 1856910058928070412348686336, 1895595685155738545939283968, 475368975085586025561263702016, 25234164906200447133548468502528,
    25234174615385935913539027861504, 159709470488148352395130183876608, 580519586160057210152057040797696, 159723641351323048177878507192320, 28092850882760264690292196638720, 1110217649257120662337445383110656,
    1110217711649026634011197946462208, 28093038058478179711549886693376, 271725940231814856742981861376, 48606904831104813707309501906944, 503029868551357936571381064925184, 48606931082740091979667244843008,
    271725940231814856742981861376, 44359082042554208219977220096, 8710352875783655095866629292032, 8710352956063885304650597924864, 44359001762323999436008587264
  ]
def positiveScales : Array ℕ := #[
    9, 5, 6, 8, 9, 10,
    6, 9, 10, 6, 8, 6,
    1, 3, 4, 5, 5, 10,
    5, 5, 5, 4, 4, 5,
    10, 5, 1, 5, 1, 30,
    30, 34, 36, 33, 31, 36,
    36, 31, 24, 29, 36, 33,
    24, 23, 30, 27, 20
  ]
def negativeArguments : Array ℕ := #[
    13, 3, 1, 3, 637, 11359,
    28735, 7583, 221
  ]
def negativeCoefficients : Array ℕ := #[
    32958915605933964438914283339776, 475368975085586025561263702016, 158456325028528675187087900672, 475368975085586025561263702016, 50468339521586383047087496364032, 899952697999528610725065731866624,
    2276621249847385740750485412904960, 600787156345666471971843775397888, 17509423915652418608173213024256
  ]
def negativeScales : Array ℕ := #[
    3, 1, 0, 1, 9, 13,
    14, 12, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9255028569818729, 5285402218862248, 6539158811107971, 8154818109052103, 9719388820935039, 10877284133344468,
    6539158811107971, 9874981347482478, 10900112062706946, 6539158811107971, 8154818109052103, 6539158811107971,
    1584962500720924, 3169925001442312, 4247927513443585, 5614709844114682, 5357552004618083, 10163649676015824,
    5129283016944966, 5357552004618083, 5209453365628949, 4247927513443585, 4247927513443585, 5209453365628949,
    10163649676015824, 5209453365628949, 1584962500720924, 5614709844114682, 1584962500720924, 30315149284708133,
    30315149839804413, 34977148899926996, 36839043779332910, 33977276903148612, 31469973979134536, 36774469664342102,
    36774469745418538, 31469983591422785, 24778067050272797, 29260932211265560, 36632343102293504, 33260932990436625,
    24778067050272797, 23163216167829144, 30780574013389588, 27780574026686396, 20163213556864501
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    3700439718214233, 1584962500724866, 0, 1584962500724866, 9315149562256301, 13471548210999231,
    14810521429522158, 12888553011131332, 7787902559895231
  ]

abbrev PositiveTerm := Fin 47
abbrev NegativeTerm := Fin 9
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
noncomputable def positiveFloor : ℝ := 838718798511 / 500000000000
noncomputable def negativeCeiling : ℝ := 326896107721 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 378190682001683673981682450432, coefficient := 378190682001683673981682450432 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 32958915605933964438914283339776, coefficient := (-32958915605933964438914283339776) }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 65223965819848473233747607552, coefficient := 65223965819848473233747607552 }, { argument := 72767662934243759283914145792, coefficient := 72767662934243759283914145792 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 72651606055560754883142352896, coefficient := 72651606055560754883142352896 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 88203227799083344586562600960, coefficient := 88203227799083344586562600960 }, { argument := 3597763239173136423925579776, coefficient := 3597763239173136423925579776 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1392682544196052809261514752, coefficient := 1392682544196052809261514752 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1895595685155738545939283968, coefficient := 1895595685155738545939283968 }, { argument := 25377770805350295635432046592, coefficient := 25377770805350295635432046592 }, { argument := 44372413283135349228415483904, coefficient := 44372413283135349228415483904 }, { argument := 1353996917968384675670917120, coefficient := 1353996917968384675670917120 }, { argument := 25377770805350295635432046592, coefficient := 25377770805350295635432046592 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1470053796651389076442710016, coefficient := 1470053796651389076442710016 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 44372413283135349228415483904, coefficient := 44372413283135349228415483904 }, { argument := 1431368170423720942852112384, coefficient := 1431368170423720942852112384 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1895595685155738545939283968, coefficient := 1895595685155738545939283968 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 475368975085586025561263702016, coefficient := 475368975085586025561263702016 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 25234164906200447133548468502528, coefficient := 25234164906200447133548468502528 }, { argument := 25234174615385935913539027861504, coefficient := 25234174615385935913539027861504 }, { argument := 50468339521586383047087496364032, coefficient := (-50468339521586383047087496364032) }, { argument := 159709470488148352395130183876608, coefficient := 159709470488148352395130183876608 }, { argument := 580519586160057210152057040797696, coefficient := 580519586160057210152057040797696 }, { argument := 159723641351323048177878507192320, coefficient := 159723641351323048177878507192320 }, { argument := 899952697999528610725065731866624, coefficient := (-899952697999528610725065731866624) }, { argument := 28092850882760264690292196638720, coefficient := 28092850882760264690292196638720 }, { argument := 1110217649257120662337445383110656, coefficient := 1110217649257120662337445383110656 }, { argument := 1110217711649026634011197946462208, coefficient := 1110217711649026634011197946462208 }, { argument := 28093038058478179711549886693376, coefficient := 28093038058478179711549886693376 }, { argument := 2276621249847385740750485412904960, coefficient := (-2276621249847385740750485412904960) }, { argument := 271725940231814856742981861376, coefficient := 271725940231814856742981861376 }, { argument := 48606904831104813707309501906944, coefficient := 48606904831104813707309501906944 }, { argument := 503029868551357936571381064925184, coefficient := 503029868551357936571381064925184 }, { argument := 48606931082740091979667244843008, coefficient := 48606931082740091979667244843008 }, { argument := 271725940231814856742981861376, coefficient := 271725940231814856742981861376 }, { argument := 600787156345666471971843775397888, coefficient := (-600787156345666471971843775397888) }, { argument := 44359082042554208219977220096, coefficient := 44359082042554208219977220096 }, { argument := 8710352875783655095866629292032, coefficient := 8710352875783655095866629292032 }, { argument := 8710352956063885304650597924864, coefficient := 8710352956063885304650597924864 }, { argument := 44359001762323999436008587264, coefficient := 44359001762323999436008587264 }, { argument := 17509423915652418608173213024256, coefficient := (-17509423915652418608173213024256) }] }

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

end TermShard8


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
