import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
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

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-146718361108436872907820812468224)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    253413, 4043729, 3833647, 4043729, 3833647, 9183771,
    264333323, 248819317, 264333323, 248819317, 1404513056535, 332430231,
    7872846174441, 416941917, 15292515, 416726877, 324898329, 1407339714327,
    332430231, 1868433, 73470195, 2784984025, 2623284135, 2784984025,
    2623284135, 113107846269161, 14700672105, 619186775451415, 23557609635, 732233629,
    23557388451, 15782011367, 113345537779945, 14700672105, 87902319, 3255,
    38955, 58275, 16905, 3255, 67515, 33915,
    3255, 38955, 3255, 1404513056535, 113107846269161, 3255,
    2883, 134943, 36735, 56553941799177, 134943, 3255,
    3255, 1395, 3255, 36735, 1395, 702237863671,
    2883, 2883, 34503, 51615
  ]
def negativeCoefficients : Array ℕ := #[
    9573672460187563220306755584, 149187267932874902893232128, 141436610155888802848047104, 149187267932874902893232128, 141436610155888802848047104, 346953058854001955950641020928,
    19504356638136810861989199872, 18359625045176833157877465088, 19504356638136810861989199872, 18359625045176833157877465088, 395335279878001398864936960, 766531924202643408826662912,
    4432018387194715318719086592, 961402604562606218998185984, 35262138806045552966369280, 960906756081904906250747904, 749164540629860768922206208, 396130913314173593176768512,
    766531924202643408826662912, 34466505369873358654537728, 346953186357896993431061790720, 205495550234178094961891737600, 193564204283870149408865648640, 205495550234178094961891737600,
    193564204283870149408865648640, 31837028394404551613392879616, 33897442004057008664173608960, 348571166399466446772481556480, 54320149490649910417576427520, 1688415794540823558968311808,
    54319639475069760495893348352, 36390840581928003682523152384, 31903932606866798652864593920, 33897442004057008664173608960, 1621511582078576519496597504, 15371302901740695170580480,
    367919572680374058599055360, 275195906789228574828134400, 319326421571645409350123520, 15371302901740695170580480, 318830573090944096602685440, 320318118533048034844999680,
    15371302901740695170580480, 367919572680374058599055360, 15371302901740695170580480, 395335279878001398864936960, 31837028394404551613392879616, 15371302901740695170580480,
    13614582570113187151085568, 637250300297878534071779328, 173476132748216416925122560, 31837038901638281915975860224, 637250300297878534071779328, 15371302901740695170580480,
    15371302901740695170580480, 13175402487206310146211840, 15371302901740695170580480, 173476132748216416925122560, 13175402487206310146211840, 395324772644271096281956352,
    13614582570113187151085568, 13614582570113187151085568, 325871621516902737616306176, 243744946013316737704919040
  ]
def negativeScales : Array ℕ := #[
    17, 21, 21, 21, 21, 23,
    27, 27, 27, 27, 40, 28,
    42, 28, 23, 28, 28, 40,
    28, 20, 26, 31, 31, 31,
    31, 46, 33, 49, 34, 29,
    34, 33, 46, 33, 26, 11,
    15, 15, 14, 11, 16, 15,
    11, 15, 11, 40, 46, 11,
    11, 17, 15, 45, 17, 11,
    11, 10, 11, 15, 10, 39,
    11, 11, 15, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    17951131021199719, 21947254894158012, 21870286072458942, 21947254894158012, 21870286072458942, 23130655237765982,
    27977783084448744, 27890523255717960, 27977783084448744, 27890523255717960, 40353207174654663, 28308476344969494,
    42840022430123258, 28635271179012472, 23866322357744780, 28634526909463646, 28275413082792111, 40356107757924708,
    28308476344969494, 20833397401733542, 26130655767950681, 31375021906104757, 31288726932254375, 31375021906104757,
    31288726932254375, 46684692340745156, 33775163064891623, 49137367987252935, 34455474106773519, 29447728792339074,
    34455460561148011, 33877562035727704, 46687720924236380, 33775163064891623, 26389397890623090, 11668441828086828,
    15249520894286927, 15830589480093830, 14045162395780740, 11668441828086828, 16042920444994070, 15049635872360048,
    11668441828086828, 15249520894286927, 11668441828086828, 40353207174654663, 46684692340745156, 11668441828086828,
    11493355121495124, 17041990615174776, 15164867654172497, 45684692816880407, 17041990615174776, 11668441828086828,
    11668441828086828, 10446049406716591, 11668441828086828, 15164867654172497, 10446049406716591, 39353168830150097,
    11493355121495124, 11493355121495124, 15074434187728835, 15655502772369993
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
noncomputable def negativeCeiling : ℝ := 905720067 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9573672460187563220306755584, coefficient := (-9573672460187563220306755584) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 149187267932874902893232128, coefficient := (-149187267932874902893232128) }, { argument := 141436610155888802848047104, coefficient := (-141436610155888802848047104) }, { argument := 346953058854001955950641020928, coefficient := (-346953058854001955950641020928) }, { argument := 19504356638136810861989199872, coefficient := (-19504356638136810861989199872) }, { argument := 18359625045176833157877465088, coefficient := (-18359625045176833157877465088) }, { argument := 19504356638136810861989199872, coefficient := (-19504356638136810861989199872) }, { argument := 18359625045176833157877465088, coefficient := (-18359625045176833157877465088) }, { argument := 395335279878001398864936960, coefficient := (-395335279878001398864936960) }, { argument := 766531924202643408826662912, coefficient := (-766531924202643408826662912) }, { argument := 4432018387194715318719086592, coefficient := (-4432018387194715318719086592) }, { argument := 961402604562606218998185984, coefficient := (-961402604562606218998185984) }, { argument := 35262138806045552966369280, coefficient := (-35262138806045552966369280) }, { argument := 960906756081904906250747904, coefficient := (-960906756081904906250747904) }, { argument := 749164540629860768922206208, coefficient := (-749164540629860768922206208) }, { argument := 396130913314173593176768512, coefficient := (-396130913314173593176768512) }, { argument := 766531924202643408826662912, coefficient := (-766531924202643408826662912) }, { argument := 34466505369873358654537728, coefficient := (-34466505369873358654537728) }, { argument := 346953186357896993431061790720, coefficient := (-346953186357896993431061790720) }, { argument := 205495550234178094961891737600, coefficient := (-205495550234178094961891737600) }, { argument := 193564204283870149408865648640, coefficient := (-193564204283870149408865648640) }, { argument := 205495550234178094961891737600, coefficient := (-205495550234178094961891737600) }, { argument := 193564204283870149408865648640, coefficient := (-193564204283870149408865648640) }, { argument := 31837028394404551613392879616, coefficient := (-31837028394404551613392879616) }, { argument := 33897442004057008664173608960, coefficient := (-33897442004057008664173608960) }, { argument := 348571166399466446772481556480, coefficient := (-348571166399466446772481556480) }, { argument := 54320149490649910417576427520, coefficient := (-54320149490649910417576427520) }, { argument := 1688415794540823558968311808, coefficient := (-1688415794540823558968311808) }, { argument := 54319639475069760495893348352, coefficient := (-54319639475069760495893348352) }, { argument := 36390840581928003682523152384, coefficient := (-36390840581928003682523152384) }, { argument := 31903932606866798652864593920, coefficient := (-31903932606866798652864593920) }, { argument := 33897442004057008664173608960, coefficient := (-33897442004057008664173608960) }, { argument := 1621511582078576519496597504, coefficient := (-1621511582078576519496597504) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 275195906789228574828134400, coefficient := (-275195906789228574828134400) }, { argument := 319326421571645409350123520, coefficient := (-319326421571645409350123520) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 318830573090944096602685440, coefficient := (-318830573090944096602685440) }, { argument := 320318118533048034844999680, coefficient := (-320318118533048034844999680) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 395335279878001398864936960, coefficient := (-395335279878001398864936960) }, { argument := 31837028394404551613392879616, coefficient := (-31837028394404551613392879616) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 31837038901638281915975860224, coefficient := (-31837038901638281915975860224) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 15371302901740695170580480, coefficient := (-15371302901740695170580480) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 395324772644271096281956352, coefficient := (-395324772644271096281956352) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 243744946013316737704919040, coefficient := (-243744946013316737704919040) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-58791721774945895338976621887488)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    14973, 2883, 59799, 30039, 2883, 34503,
    2883, 134943, 1614963, 2415915, 700833, 134943,
    2798979, 1406019, 134943, 1614963, 134943, 36735,
    439635, 657675, 190785, 36735, 761955, 382755,
    36735, 439635, 36735, 332430231, 14700672105, 38955,
    34503, 1614963, 439635, 7350334299, 1614963, 38955,
    38955, 16695, 38955, 439635, 16695, 166216869,
    34503, 2027277, 264333387, 248819381, 264333387, 248819381,
    56553941799177, 7350334299, 309593469533943, 11778801993, 366116727, 11778691401,
    7891003797, 56672787525897, 7350334299, 43951149, 134943, 1614963,
    2415915, 700833, 134943, 2798979
  ]
def negativeCoefficients : Array ℕ := #[
    282831973392028791138680832, 13614582570113187151085568, 282392793309121914133807104, 283710333557842545148428288, 13614582570113187151085568, 325871621516902737616306176,
    13614582570113187151085568, 637250300297878534071779328, 15252894284549221686492266496, 11408836021462018916446371840, 13238361077155928256200835072, 637250300297878534071779328,
    13217804615855996690585616384, 13279473999755791387431272448, 637250300297878534071779328, 15252894284549221686492266496, 637250300297878534071779328, 173476132748216416925122560,
    4152235177392792947046481920, 3105782376621293915917516800, 3603826757737141048379965440, 173476132748216416925122560, 3598230753454940518801735680, 3615018766301542107536424960,
    173476132748216416925122560, 4152235177392792947046481920, 173476132748216416925122560, 766531924202643408826662912, 33897442004057008664173608960, 367919572680374058599055360,
    325871621516902737616306176, 15252894284549221686492266496, 4152235177392792947046481920, 33897433917465575351748919296, 15252894284549221686492266496, 367919572680374058599055360,
    367919572680374058599055360, 315359633726034907370618880, 367919572680374058599055360, 4152235177392792947046481920, 315359633726034907370618880, 766540010794076721251352576,
    325871621516902737616306176, 9573544956292525739885985792, 19504361360503293731634413568, 18359629767543316027522678784, 19504361360503293731634413568, 18359629767543316027522678784,
    31837038901638281915975860224, 33897433917465575351748919296, 348571258507351175181927186432, 54320136464942751369419292672, 1688415391018296946571870208, 54319626449362601447736213504,
    36390831881982329919255871488, 31903943097959627890951716864, 33897433917465575351748919296, 1621511194696950971596013568, 637250300297878534071779328, 15252894284549221686492266496,
    11408836021462018916446371840, 13238361077155928256200835072, 637250300297878534071779328, 13217804615855996690585616384
  ]
def negativeScales : Array ℕ := #[
    13, 11, 15, 14, 11, 15,
    11, 17, 20, 21, 19, 17,
    21, 20, 17, 20, 17, 15,
    18, 19, 17, 15, 19, 18,
    15, 18, 15, 28, 33, 15,
    15, 20, 18, 32, 20, 15,
    15, 14, 15, 18, 14, 27,
    15, 20, 27, 27, 27, 27,
    45, 32, 48, 33, 28, 33,
    32, 45, 32, 25, 17, 20,
    21, 19, 17, 21
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    13870075691751301, 11493355121495124, 15867833740861174, 14874549168549452, 11493355121495124, 15074434187728835,
    11493355121495124, 17041990615174776, 20623069681419278, 21204138266025370, 19418711182902532, 17041990615174776,
    21416469232115861, 20423184659481843, 17041990615174776, 20623069681419278, 17041990615174776, 15164867654172497,
    18745946720612189, 19327015305023091, 17541588221901267, 15164867654172497, 19539346271114529, 18546061698480726,
    15164867654172497, 18745946720612189, 15164867654172497, 28308476344969494, 33775163064891623, 15249520894286927,
    15074434187728835, 20623069681419278, 18745946720612189, 32775162720721498, 20623069681419278, 15249520894286927,
    15249520894286927, 14027128472950479, 15249520894286927, 18745946720612189, 14027128472950479, 27308491564718929,
    15074434187728835, 20951111806995793, 27977783433752022, 27890523626800390, 27977783433752022, 27890523626800390,
    45684692816880407, 32775162720721498, 48137368368476581, 33455473760822236, 28447728447542479, 33455460215193481,
    32877561690823039, 45687721398643260, 32775162720721498, 25389397545960972, 17041990615174776, 20623069681419278,
    21204138266025370, 19418711182902532, 17041990615174776, 21416469232115861
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
noncomputable def negativeCeiling : ℝ := 85615041 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 282831973392028791138680832, coefficient := (-282831973392028791138680832) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 282392793309121914133807104, coefficient := (-282392793309121914133807104) }, { argument := 283710333557842545148428288, coefficient := (-283710333557842545148428288) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 13614582570113187151085568, coefficient := (-13614582570113187151085568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 11408836021462018916446371840, coefficient := (-11408836021462018916446371840) }, { argument := 13238361077155928256200835072, coefficient := (-13238361077155928256200835072) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 13217804615855996690585616384, coefficient := (-13217804615855996690585616384) }, { argument := 13279473999755791387431272448, coefficient := (-13279473999755791387431272448) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 3105782376621293915917516800, coefficient := (-3105782376621293915917516800) }, { argument := 3603826757737141048379965440, coefficient := (-3603826757737141048379965440) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 3598230753454940518801735680, coefficient := (-3598230753454940518801735680) }, { argument := 3615018766301542107536424960, coefficient := (-3615018766301542107536424960) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 173476132748216416925122560, coefficient := (-173476132748216416925122560) }, { argument := 766531924202643408826662912, coefficient := (-766531924202643408826662912) }, { argument := 33897442004057008664173608960, coefficient := (-33897442004057008664173608960) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 33897433917465575351748919296, coefficient := (-33897433917465575351748919296) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 367919572680374058599055360, coefficient := (-367919572680374058599055360) }, { argument := 4152235177392792947046481920, coefficient := (-4152235177392792947046481920) }, { argument := 315359633726034907370618880, coefficient := (-315359633726034907370618880) }, { argument := 766540010794076721251352576, coefficient := (-766540010794076721251352576) }, { argument := 325871621516902737616306176, coefficient := (-325871621516902737616306176) }, { argument := 9573544956292525739885985792, coefficient := (-9573544956292525739885985792) }, { argument := 19504361360503293731634413568, coefficient := (-19504361360503293731634413568) }, { argument := 18359629767543316027522678784, coefficient := (-18359629767543316027522678784) }, { argument := 19504361360503293731634413568, coefficient := (-19504361360503293731634413568) }, { argument := 18359629767543316027522678784, coefficient := (-18359629767543316027522678784) }, { argument := 31837038901638281915975860224, coefficient := (-31837038901638281915975860224) }, { argument := 33897433917465575351748919296, coefficient := (-33897433917465575351748919296) }, { argument := 348571258507351175181927186432, coefficient := (-348571258507351175181927186432) }, { argument := 54320136464942751369419292672, coefficient := (-54320136464942751369419292672) }, { argument := 1688415391018296946571870208, coefficient := (-1688415391018296946571870208) }, { argument := 54319626449362601447736213504, coefficient := (-54319626449362601447736213504) }, { argument := 36390831881982329919255871488, coefficient := (-36390831881982329919255871488) }, { argument := 31903943097959627890951716864, coefficient := (-31903943097959627890951716864) }, { argument := 33897433917465575351748919296, coefficient := (-33897433917465575351748919296) }, { argument := 1621511194696950971596013568, coefficient := (-1621511194696950971596013568) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 15252894284549221686492266496, coefficient := (-15252894284549221686492266496) }, { argument := 11408836021462018916446371840, coefficient := (-11408836021462018916446371840) }, { argument := 13238361077155928256200835072, coefficient := (-13238361077155928256200835072) }, { argument := 637250300297878534071779328, coefficient := (-637250300297878534071779328) }, { argument := 13217804615855996690585616384, coefficient := (-13217804615855996690585616384) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
