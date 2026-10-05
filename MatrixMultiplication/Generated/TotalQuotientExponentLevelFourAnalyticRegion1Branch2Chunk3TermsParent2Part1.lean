import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 3, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3

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
def constantNumerator : ℤ := (-65324599301950685807280218177536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1406019, 134943, 1614963, 134943, 7872846174441, 619186775451415,
    58275, 51615, 2415915, 657675, 309593469533943, 2415915,
    58275, 58275, 24975, 58275, 657675, 24975,
    3936341278985, 51615, 3255, 38955, 58275, 16905,
    3255, 67515, 33915, 3255, 38955, 3255,
    416941917, 23557609635, 16905, 14973, 700833, 190785,
    11778801993, 700833, 16905, 16905, 7245, 16905,
    190785, 7245, 208473783, 14973, 4043729, 264333323,
    2784984025, 264333387, 4043729, 3255, 38955, 58275,
    16905, 3255, 67515, 33915, 3255, 38955,
    3255, 1395, 16695, 24975
  ]
def negativeCoefficients : Array ℕ := #[
    13279473999755791387431272448, 637250300297878534071779328, 15252894284549221686492266496, 637250300297878534071779328, 4432018387194715318719086592, 348571166399466446772481556480,
    275195906789228574828134400, 243744946013316737704919040, 11408836021462018916446371840, 3105782376621293915917516800, 348571258507351175181927186432, 11408836021462018916446371840,
    275195906789228574828134400, 275195906789228574828134400, 235882205819338778424115200, 275195906789228574828134400, 3105782376621293915917516800, 235882205819338778424115200,
    4431926279309986909273456640, 243744946013316737704919040, 15371302901740695170580480, 367919572680374058599055360, 275195906789228574828134400, 319326421571645409350123520,
    15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680, 15371302901740695170580480, 367919572680374058599055360, 15371302901740695170580480,
    961402604562606218998185984, 54320149490649910417576427520, 319326421571645409350123520, 282831973392028791138680832, 13238361077155928256200835072, 3603826757737141048379965440,
    54320136464942751369419292672, 13238361077155928256200835072, 319326421571645409350123520, 319326421571645409350123520, 273708361347124636585820160, 319326421571645409350123520,
    3603826757737141048379965440, 273708361347124636585820160, 961415630269765267155320832, 282831973392028791138680832, 149187267932874902893232128, 19504356638136810861989199872,
    205495550234178094961891737600, 19504361360503293731634413568, 149187267932874902893232128, 15371302901740695170580480, 367919572680374058599055360, 275195906789228574828134400,
    319326421571645409350123520, 15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680, 15371302901740695170580480, 367919572680374058599055360,
    15371302901740695170580480, 13175402487206310146211840, 315359633726034907370618880, 235882205819338778424115200
  ]
def negativeScales : Array ℕ := #[
    20, 17, 20, 17, 42, 49,
    15, 15, 21, 19, 48, 21,
    15, 15, 14, 15, 19, 14,
    41, 15, 11, 15, 15, 14,
    11, 16, 15, 11, 15, 11,
    28, 34, 14, 13, 19, 17,
    33, 19, 14, 14, 12, 14,
    17, 12, 27, 13, 21, 27,
    31, 27, 21, 11, 15, 15,
    14, 11, 16, 15, 11, 15,
    11, 10, 14, 14
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    20423184659481843, 17041990615174776, 20623069681419278, 17041990615174776, 42840022430123258, 49137367987252935,
    15830589480093830, 15655502772369993, 21204138266025370, 19327015305023091, 48137368368476581, 21204138266025370,
    15830589480093830, 15830589480093830, 14608197057574227, 15830589480093830, 19327015305023091, 14608197057574227,
    41839992447176116, 15655502772369993, 11668441828086828, 15249520894286927, 15830589480093830, 14045162395780740,
    11668441828086828, 16042920444994070, 15049635872360048, 11668441828086828, 15249520894286927, 11668441828086828,
    28635271179012472, 34455474106773519, 14045162395780740, 13870075691751301, 19418711182902532, 17541588221901267,
    33455473760822236, 19418711182902532, 14045162395780740, 14045162395780740, 12822769975464802, 14045162395780740,
    17541588221901267, 12822769975464802, 27635290725449872, 13870075691751301, 21947254894158012, 27977783084448744,
    31375021906104757, 27977783433752022, 21947254894158012, 11668441828086828, 15249520894286927, 15830589480093830,
    14045162395780740, 11668441828086828, 16042920444994070, 15049635872360048, 11668441828086828, 15249520894286927,
    11668441828086828, 10446049406716591, 14027128472950479, 14608197057574227
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
noncomputable def negativeCeiling : ℝ := 572446549 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13279473999755791387431272448, coefficient := (-13279473999755791387431272448) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 4432018387194715318719086592, coefficient := (-4432018387194715318719086592) }, { argument := 348571166399466446772481556480, coefficient := (-348571166399466446772481556480) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 11408836021462018916446371840, coefficient := (-11408836021462018916446371840) }, { argument := 3105782376621293915917516800, coefficient := (-3105782376621293915917516800) }, { argument := 348571258507351175181927186432, coefficient := (-348571258507351175181927186432) }, { argument := 11408836021462018916446371840, coefficient := (-11408836021462018916446371840) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 235882205819338778424115200, coefficient := (-235882205819338778424115200) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 3105782376621293915917516800, coefficient := (-3105782376621293915917516800) }, { argument := 235882205819338778424115200, coefficient := (-235882205819338778424115200) }, { argument := 4431926279309986909273456640, coefficient := (-4431926279309986909273456640) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 961402604562606218998185984, coefficient := (-961402604562606218998185984) }, { argument := 54320149490649910417576427520, coefficient := (-54320149490649910417576427520) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 282831973392028791138680832, coefficient := (-282831973392028791138680832) }, { argument := 13238361077155928256200835072, coefficient := (-13238361077155928256200835072) }, { argument := 3603826757737141048379965440, coefficient := (-3603826757737141048379965440) }, { argument := 54320136464942751369419292672, coefficient := (-54320136464942751369419292672) }, { argument := 13238361077155928256200835072, coefficient := (-13238361077155928256200835072) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 273708361347124636585820160, coefficient := (-273708361347124636585820160) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 3603826757737141048379965440, coefficient := (-3603826757737141048379965440) }, { argument := 273708361347124636585820160, coefficient := (-273708361347124636585820160) }, { argument := 961415630269765267155320832, coefficient := (-961415630269765267155320832) }, { argument := 282831973392028791138680832, coefficient := (-282831973392028791138680832) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 19504356638136810861989199872, coefficient := (-19504356638136810861989199872) }, { argument := 205495550234178094961891737600, coefficient := (-205495550234178094961891737600) }, { argument := 19504361360503293731634413568, coefficient := (-19504361360503293731634413568) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 235882205819338778424115200, coefficient := (-235882205819338778424115200) }] }

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
def constantNumerator : ℤ := (-11697878794583920070534363086848)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7245, 1395, 28935, 14535, 1395, 16695,
    1395, 15292515, 732233629, 3255, 2883, 134943,
    36735, 366116727, 134943, 3255, 3255, 1395,
    3255, 36735, 1395, 7646345, 2883, 3255,
    38955, 58275, 16905, 3255, 67515, 33915,
    3255, 38955, 3255, 36735, 439635, 657675,
    190785, 36735, 761955, 382755, 36735, 439635,
    36735, 416726877, 23557388451, 67515, 59799, 2798979,
    761955, 11778691401, 2798979, 67515, 67515, 28935,
    67515, 761955, 28935, 208366263, 59799, 1395,
    16695, 24975, 7245, 1395
  ]
def negativeCoefficients : Array ℕ := #[
    273708361347124636585820160, 13175402487206310146211840, 273283348363666368516587520, 274558387314041172724285440, 13175402487206310146211840, 315359633726034907370618880,
    13175402487206310146211840, 35262138806045552966369280, 1688415794540823558968311808, 15371302901740695170580480, 13614582570113187151085568, 637250300297878534071779328,
    173476132748216416925122560, 1688415391018296946571870208, 637250300297878534071779328, 15371302901740695170580480, 15371302901740695170580480, 13175402487206310146211840,
    15371302901740695170580480, 173476132748216416925122560, 13175402487206310146211840, 35262542328572165362810880, 13614582570113187151085568, 15371302901740695170580480,
    367919572680374058599055360, 275195906789228574828134400, 319326421571645409350123520, 15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680,
    15371302901740695170580480, 367919572680374058599055360, 15371302901740695170580480, 173476132748216416925122560, 4152235177392792947046481920, 3105782376621293915917516800,
    3603826757737141048379965440, 173476132748216416925122560, 3598230753454940518801735680, 3615018766301542107536424960, 173476132748216416925122560, 4152235177392792947046481920,
    173476132748216416925122560, 960906756081904906250747904, 54319639475069760495893348352, 318830573090944096602685440, 282392793309121914133807104, 13217804615855996690585616384,
    3598230753454940518801735680, 54319626449362601447736213504, 13217804615855996690585616384, 318830573090944096602685440, 318830573090944096602685440, 273283348363666368516587520,
    318830573090944096602685440, 3598230753454940518801735680, 273283348363666368516587520, 960919781789063954407882752, 282392793309121914133807104, 13175402487206310146211840,
    315359633726034907370618880, 235882205819338778424115200, 273708361347124636585820160, 13175402487206310146211840
  ]
def negativeScales : Array ℕ := #[
    12, 10, 14, 13, 10, 14,
    10, 23, 29, 11, 11, 17,
    15, 28, 17, 11, 11, 10,
    11, 15, 10, 22, 11, 11,
    15, 15, 14, 11, 16, 15,
    11, 15, 11, 15, 18, 19,
    17, 15, 19, 18, 15, 18,
    15, 28, 34, 16, 15, 21,
    19, 33, 21, 16, 16, 14,
    16, 19, 14, 27, 15, 10,
    14, 14, 12, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    12822769975464802, 10446049406716591, 14820528024633809, 13827243452138220, 10446049406716591, 14027128472950479,
    10446049406716591, 23866322357744780, 29447728792339074, 11668441828086828, 11493355121495124, 17041990615174776,
    15164867654172497, 28447728447542479, 17041990615174776, 11668441828086828, 11668441828086828, 10446049406716591,
    11668441828086828, 15164867654172497, 10446049406716591, 22866338867141613, 11493355121495124, 11668441828086828,
    15249520894286927, 15830589480093830, 14045162395780740, 11668441828086828, 16042920444994070, 15049635872360048,
    11668441828086828, 15249520894286927, 11668441828086828, 15164867654172497, 18745946720612189, 19327015305023091,
    17541588221901267, 15164867654172497, 19539346271114529, 18546061698480726, 15164867654172497, 18745946720612189,
    15164867654172497, 28634526909463646, 34455460561148011, 16042920444994070, 15867833740861174, 21416469232115861,
    19539346271114529, 33455460215193481, 21416469232115861, 16042920444994070, 16042920444994070, 14820528024633809,
    16042920444994070, 19539346271114529, 14820528024633809, 27634546465987359, 15867833740861174, 10446049406716591,
    14027128472950479, 14608197057574227, 12822769975464802, 10446049406716591
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
noncomputable def negativeCeiling : ℝ := 15348161 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 273708361347124636585820160, coefficient := (-273708361347124636585820160) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 274558387314041172724285440, coefficient := (-274558387314041172724285440) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 35262138806045552966369280, coefficient := (-35262138806045552966369280) }, { argument := 1688415794540823558968311808, coefficient := (-1688415794540823558968311808) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 1688415391018296946571870208, coefficient := (-1688415391018296946571870208) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 35262542328572165362810880, coefficient := (-35262542328572165362810880) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 3105782376621293915917516800, coefficient := (-3105782376621293915917516800) }, { argument := 3603826757737141048379965440, coefficient := (-3603826757737141048379965440) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 3598230753454940518801735680, coefficient := (-3598230753454940518801735680) }, { argument := 3615018766301542107536424960, coefficient := (-3615018766301542107536424960) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 960906756081904906250747904, coefficient := (-960906756081904906250747904) }, { argument := 54319639475069760495893348352, coefficient := (-54319639475069760495893348352) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 13217804615855996690585616384, coefficient := (-13217804615855996690585616384) }, { argument := 3598230753454940518801735680, coefficient := (-3598230753454940518801735680) }, { argument := 54319626449362601447736213504, coefficient := (-54319626449362601447736213504) }, { argument := 13217804615855996690585616384, coefficient := (-13217804615855996690585616384) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 3598230753454940518801735680, coefficient := (-3598230753454940518801735680) }, { argument := 273283348363666368516587520, coefficient := (-273283348363666368516587520) }, { argument := 960919781789063954407882752, coefficient := (-960919781789063954407882752) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 235882205819338778424115200, coefficient := (-235882205819338778424115200) }, { argument := 273708361347124636585820160, coefficient := (-273708361347124636585820160) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
