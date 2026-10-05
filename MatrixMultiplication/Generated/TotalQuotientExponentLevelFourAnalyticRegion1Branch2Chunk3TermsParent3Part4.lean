import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 2,
parent chunk 3, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 4287489089422599898948322201698304
def positiveArguments : Array ℕ := #[
    441, 5, 1, 1, 1, 1,
    93, 1113, 1665, 483, 93, 1929,
    969, 93, 1113, 93, 3891015, 6594745,
    3891015, 965115, 8671617, 138745927, 3860413, 1038167,
    28782127, 459, 294211565, 471, 15, 459,
    261, 471, 7353, 9, 57564273, 459,
    15, 9, 15, 231, 261
  ]
def positiveCoefficients : Array ℕ := #[
    34939619668790572878752882098176, 792281625142643375935439503360, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672, 158456325028528675187087900672,
    7195526478346272847851159552, 172228407965578530745340657664, 128823135338134884856690114560, 149481259743709668194069250048, 7195526478346272847851159552, 149249145986343659392525664256,
    149945487258441685797156421632, 7195526478346272847851159552, 172228407965578530745340657664, 7195526478346272847851159552, 146998390562744260569354731520, 498284844017154854796730040320,
    146998390562744260569354731520, 36461013824917901123329720320, 1310417711138643975009755725824, 1310418230598957090670729232384, 36460569922468511376679632896, 9805210088842661925134270464,
    1087358014803979623884323291136, 35513404876999346636168626176, 11114998667428992074530076753920, 36441859906463381842342969344, 1160568786830044007717928960, 35513404876999346636168626176,
    20193896890842765734291963904, 36441859906463381842342969344, 568910819304087572583328776192, 22282920707136844948184236032, 1087358373703832321977359532032, 35513404876999346636168626176,
    1160568786830044007717928960, 22282920707136844948184236032, 1160568786830044007717928960, 35745518634365355437712211968, 20193896890842765734291963904
  ]
def positiveScales : Array ℕ := #[
    8, 2, 0, 0, 0, 0,
    6, 10, 10, 8, 6, 10,
    9, 6, 10, 6, 21, 22,
    21, 19, 23, 27, 21, 19,
    24, 8, 28, 8, 3, 8,
    8, 8, 12, 3, 25, 8,
    3, 3, 3, 7, 8
  ]
def negativeArguments : Array ℕ := #[
    14601, 227943, 279, 25175649, 14229, 465,
    279, 465, 7161, 8091, 457971, 238650497,
    8574630527, 68597071479, 1909180809, 3891015, 6594745, 3891015,
    5, 1, 3, 5, 17
  ]
def negativeCoefficients : Array ℕ := #[
    137902546032759379530350592, 2152860766409511077891014656, 84322575918120384935755776, 1857635015970167197727195136, 134389105369504363491360768, 4391800829068770048737280,
    84322575918120384935755776, 4391800829068770048737280, 135267465535318117501108224, 76417334425796598848028672, 16896147660361674126262272, 4402324641222589126805553152,
    158174014858186259418035781632, 158174077722384219610973995008, 4402271221757594673157767168, 73499195281372130284677365760, 249142422008577427398365020160, 73499195281372130284677365760,
    792281625142643375935439503360, 633825300114114700748351602688, 950737950171172051122527404032, 792281625142643375935439503360, 2693757525484987478180494311424
  ]
def negativeScales : Array ℕ := #[
    13, 17, 8, 24, 13, 8,
    8, 8, 12, 12, 18, 27,
    32, 35, 30, 21, 22, 21,
    2, 0, 1, 2, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    8784634845528344, 2321928094887362, 0, 0, 0, 0,
    6539158811107971, 10120237877341959, 10701306461953989, 8915879378478017, 6539158811107971, 10913637427705176,
    9920352855028171, 6539158811107971, 10120237877341959, 6539158811107971, 21891715111053329, 22652885444971227,
    21891715111053329, 19880341333773201, 23047869607796079, 27047870179692096, 21880323769265486, 19985607103087524,
    24778669875407973, 8842350343321225, 28132278716909239, 8879583249426338, 3906890595303263, 8842350343321225,
    8027905996569884, 8879583249426338, 12844117269492213, 3169925001442312, 25778670351592399, 8842350343321225,
    3906890595303263, 3169925001442312, 3906890595303263, 7851749041305231, 8027905996569884
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    13833779561266426, 17798313580599046, 8124121311829188, 24585525633987105, 13796546654402698, 8861086908132560,
    8124121311829188, 8861086908132560, 12805945352531863, 12982102324703674, 18804896720894461, 27830324101151146,
    32997427384922505, 35997427958302915, 30830306594839619, 21891715115047817, 22652885444995578, 21891715115047817,
    2321928094887363, 0, 1584962500724866, 2321928094887363, 4087462841250340
  ]

abbrev PositiveTerm := Fin 41
abbrev NegativeTerm := Fin 23
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
noncomputable def positiveFloor : ℝ := 1174640157 / 125000000000
noncomputable def negativeCeiling : ℝ := 437213523 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 137902546032759379530350592, coefficient := (-137902546032759379530350592) }, { argument := 2152860766409511077891014656, coefficient := (-2152860766409511077891014656) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 1857635015970167197727195136, coefficient := (-1857635015970167197727195136) }, { argument := 134389105369504363491360768, coefficient := (-134389105369504363491360768) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 84322575918120384935755776, coefficient := (-84322575918120384935755776) }, { argument := 4391800829068770048737280, coefficient := (-4391800829068770048737280) }, { argument := 135267465535318117501108224, coefficient := (-135267465535318117501108224) }, { argument := 76417334425796598848028672, coefficient := (-76417334425796598848028672) }, { argument := 16896147660361674126262272, coefficient := (-16896147660361674126262272) }, { argument := 4402324641222589126805553152, coefficient := (-4402324641222589126805553152) }, { argument := 158174014858186259418035781632, coefficient := (-158174014858186259418035781632) }, { argument := 158174077722384219610973995008, coefficient := (-158174077722384219610973995008) }, { argument := 4402271221757594673157767168, coefficient := (-4402271221757594673157767168) }, { argument := 73499195281372130284677365760, coefficient := (-73499195281372130284677365760) }, { argument := 249142422008577427398365020160, coefficient := (-249142422008577427398365020160) }, { argument := 73499195281372130284677365760, coefficient := (-73499195281372130284677365760) }, { argument := 34939619668790572878752882098176, coefficient := 34939619668790572878752882098176 }, { argument := 792281625142643375935439503360, coefficient := 792281625142643375935439503360 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 158456325028528675187087900672, coefficient := 158456325028528675187087900672 }, { argument := 633825300114114700748351602688, coefficient := (-633825300114114700748351602688) }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 172228407965578530745340657664, coefficient := 172228407965578530745340657664 }, { argument := 128823135338134884856690114560, coefficient := 128823135338134884856690114560 }, { argument := 149481259743709668194069250048, coefficient := 149481259743709668194069250048 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 149249145986343659392525664256, coefficient := 149249145986343659392525664256 }, { argument := 149945487258441685797156421632, coefficient := 149945487258441685797156421632 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 172228407965578530745340657664, coefficient := 172228407965578530745340657664 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 950737950171172051122527404032, coefficient := (-950737950171172051122527404032) }, { argument := 146998390562744260569354731520, coefficient := 146998390562744260569354731520 }, { argument := 498284844017154854796730040320, coefficient := 498284844017154854796730040320 }, { argument := 146998390562744260569354731520, coefficient := 146998390562744260569354731520 }, { argument := 792281625142643375935439503360, coefficient := (-792281625142643375935439503360) }, { argument := 36461013824917901123329720320, coefficient := 36461013824917901123329720320 }, { argument := 1310417711138643975009755725824, coefficient := 1310417711138643975009755725824 }, { argument := 1310418230598957090670729232384, coefficient := 1310418230598957090670729232384 }, { argument := 36460569922468511376679632896, coefficient := 36460569922468511376679632896 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 9805210088842661925134270464, coefficient := 9805210088842661925134270464 }, { argument := 1087358014803979623884323291136, coefficient := 1087358014803979623884323291136 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 11114998667428992074530076753920, coefficient := 11114998667428992074530076753920 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }, { argument := 36441859906463381842342969344, coefficient := 36441859906463381842342969344 }, { argument := 568910819304087572583328776192, coefficient := 568910819304087572583328776192 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1087358373703832321977359532032, coefficient := 1087358373703832321977359532032 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 22282920707136844948184236032, coefficient := 22282920707136844948184236032 }, { argument := 1160568786830044007717928960, coefficient := 1160568786830044007717928960 }, { argument := 35745518634365355437712211968, coefficient := 35745518634365355437712211968 }, { argument := 20193896890842765734291963904, coefficient := 20193896890842765734291963904 }] }

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


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2336351052703343232662834782404608)
def positiveArguments : Array ℕ := #[
    1038167, 11900929, 697988095, 3535, 3131, 146551,
    39895, 174497055, 146551, 3535, 3535, 1515,
    3535, 39895, 1515, 2975201, 3131, 29607121,
    45591, 171289903, 73437, 2275, 73437, 49049,
    29700305, 45591, 273, 6955, 6357, 6955,
    6357
  ]
def positiveCoefficients : Array ℕ := #[
    9805210088842661925134270464, 224802192898445455773543694336, 13184622341080135184134155796480, 68376844357403426121381314560, 60562347859414463136080592896, 2834708604645496322917836783616,
    771681529176410094798446264320, 13184624702263376618956762644480, 2834708604645496322917836783616, 68376844357403426121381314560, 68376844357403426121381314560, 58608723734917222389755412480,
    68376844357403426121381314560, 771681529176410094798446264320, 58608723734917222389755412480, 224799831715204020950936846336, 60562347859414463136080592896, 559262703458664052275873316864,
    881858192672808939264468320256, 6471149574249541522387216891904, 1420478166640632363246359150592, 44004899833972501959304806400, 1420478166640632363246359150592, 948745640420447142242611625984,
    561022899452022952354245509120, 881858192672808939264468320256, 42244703840613601880932614144, 538117060826863738245213061120, 491849051858572650470858293248, 538117060826863738245213061120,
    491849051858572650470858293248
  ]
def positiveScales : Array ℕ := #[
    19, 23, 29, 11, 11, 17,
    15, 27, 17, 11, 11, 10,
    11, 15, 10, 21, 11, 24,
    15, 27, 16, 11, 16, 15,
    24, 15, 8, 12, 12, 12,
    12
  ]
def negativeArguments : Array ℕ := #[
    179, 109, 167, 13
  ]
def negativeCoefficients : Array ℕ := #[
    14181841090053316429244367110144, 34543478856219251190785162346496, 13231103139882144378121839706112, 2059932225370872777432142708736
  ]
def negativeScales : Array ℕ := #[
    7, 6, 7, 3
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    19985607103087524, 23504570860549808, 29378627188899251, 11787494499665800, 11612407793138175, 17161043286818539,
    15283920325816259, 27378627447265926, 17161043286818539, 11787494499665800, 11787494499665800, 10565102078360182,
    11787494499665800, 15283920325816259, 10565102078360182, 21504555707293521, 11612407793138175, 24819440873649245,
    15476461433393896, 27351864870700870, 16164219503476476, 11151650829973420, 16164219503476476, 15581936102950989,
    24823974410651921, 15476461433393896, 8092757140919852, 12763834799410789, 12634130373092445, 12763834799410789,
    12634130373092445
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    7483815777264413, 6768184325109843, 7383704292474056, 3700439718214233
  ]

abbrev PositiveTerm := Fin 31
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 14506971781 / 1000000000000
noncomputable def negativeCeiling : ℝ := 535947937 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9805210088842661925134270464, coefficient := 9805210088842661925134270464 }, { argument := 14181841090053316429244367110144, coefficient := (-14181841090053316429244367110144) }, { argument := 224802192898445455773543694336, coefficient := 224802192898445455773543694336 }, { argument := 13184622341080135184134155796480, coefficient := 13184622341080135184134155796480 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 60562347859414463136080592896, coefficient := 60562347859414463136080592896 }, { argument := 2834708604645496322917836783616, coefficient := 2834708604645496322917836783616 }, { argument := 771681529176410094798446264320, coefficient := 771681529176410094798446264320 }, { argument := 13184624702263376618956762644480, coefficient := 13184624702263376618956762644480 }, { argument := 2834708604645496322917836783616, coefficient := 2834708604645496322917836783616 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 58608723734917222389755412480, coefficient := 58608723734917222389755412480 }, { argument := 68376844357403426121381314560, coefficient := 68376844357403426121381314560 }, { argument := 771681529176410094798446264320, coefficient := 771681529176410094798446264320 }, { argument := 58608723734917222389755412480, coefficient := 58608723734917222389755412480 }, { argument := 224799831715204020950936846336, coefficient := 224799831715204020950936846336 }, { argument := 60562347859414463136080592896, coefficient := 60562347859414463136080592896 }, { argument := 34543478856219251190785162346496, coefficient := (-34543478856219251190785162346496) }, { argument := 559262703458664052275873316864, coefficient := 559262703458664052275873316864 }, { argument := 881858192672808939264468320256, coefficient := 881858192672808939264468320256 }, { argument := 6471149574249541522387216891904, coefficient := 6471149574249541522387216891904 }, { argument := 1420478166640632363246359150592, coefficient := 1420478166640632363246359150592 }, { argument := 44004899833972501959304806400, coefficient := 44004899833972501959304806400 }, { argument := 1420478166640632363246359150592, coefficient := 1420478166640632363246359150592 }, { argument := 948745640420447142242611625984, coefficient := 948745640420447142242611625984 }, { argument := 561022899452022952354245509120, coefficient := 561022899452022952354245509120 }, { argument := 881858192672808939264468320256, coefficient := 881858192672808939264468320256 }, { argument := 42244703840613601880932614144, coefficient := 42244703840613601880932614144 }, { argument := 13231103139882144378121839706112, coefficient := (-13231103139882144378121839706112) }, { argument := 538117060826863738245213061120, coefficient := 538117060826863738245213061120 }, { argument := 491849051858572650470858293248, coefficient := 491849051858572650470858293248 }, { argument := 538117060826863738245213061120, coefficient := 538117060826863738245213061120 }, { argument := 491849051858572650470858293248, coefficient := 491849051858572650470858293248 }, { argument := 2059932225370872777432142708736, coefficient := (-2059932225370872777432142708736) }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk3
