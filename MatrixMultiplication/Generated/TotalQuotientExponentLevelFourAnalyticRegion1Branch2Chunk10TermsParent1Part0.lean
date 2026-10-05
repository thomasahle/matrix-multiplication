import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 10, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10

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
def constantNumerator : ℤ := (-3208783355715331812801669742198784)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    535, 489, 535, 489, 1829057273, 2684879349,
    20428463497, 3891266343, 129237017, 3890479911, 2768765467, 916625789,
    2684879349, 15630339, 111940417355549, 6219232618056419, 73879727705, 67191739573,
    2895471732153, 954627009105, 3109616876846383, 2895471732153, 73879727705, 73728025665,
    32020323825, 73728025665, 954627009105, 32020323825, 55969640859601, 67191739573,
    698183343233, 334300444699991, 1597344417, 27554340908037429, 1575536581, 52937837,
    1597344417, 963283407, 1575536581, 25119854571, 32760795, 668601077679829,
    1597344417, 52937837, 32760795, 52937837, 803475701, 963283407,
    22364611048607, 13395, 56259, 243789, 8037, 8037,
    18753, 243789, 243789, 8037, 3008517, 120555,
    56259, 243789, 18753, 120555
  ]
def negativeCoefficients : Array ℕ := #[
    20696810031802451470969733120, 18917271225329717325802242048, 20696810031802451470969733120, 18917271225329717325802242048, 134960605644752413891254812672, 198109128879163635831391911936,
    1507354551793106610270773444608, 287124777407842757443848241152, 9536008709794602301037477888, 287066748968501255243462344704, 204298831879495636409739378688, 135270090728360735254817800192,
    198109128879163635831391911936, 9226523626186280937474490368, 252067410945074139824392241152, 14004466850604661440707572006912, 85177526825592757665482670080, 77466801485654581764054581248,
    3338251625980430182862530019328, 1100610007675670807603293716480, 14004469407830376029503218515968, 3338251625980430182862530019328, 85177526825592757665482670080, 85002626281384029581255639040,
    73833839844634938967484006400, 85002626281384029581255639040, 1100610007675670807603293716480, 73833839844634938967484006400, 252064853719359551028745732096, 77466801485654581764054581248,
    12577352977681703640101814272, 1505555358180670572062924865536, 29465803657967788753390927872, 15511714930734622454437902286848, 29063520088474358940115664896, 976530730954752228790894592,
    29465803657967788753390927872, 17769442479379996009102835712, 29063520088474358940115664896, 463379528440040041087538036736, 19338560032520432321078231040, 1505555782149194967349924462592,
    29465803657967788753390927872, 976530730954752228790894592, 19338560032520432321078231040, 976530730954752228790894592, 29643021251582755310122565632, 17769442479379996009102835712,
    12590156748099070375581712384, 63256099038038897637457920, 1062702463839053480309293056, 2302522004984615874003468288, 75907318845646677164949504, 1214517101530346834639192064,
    88558538653254456692441088, 2302522004984615874003468288, 2302522004984615874003468288, 1214517101530346834639192064, 28414639687887072818746097664, 2277219565369400314948485120,
    1062702463839053480309293056, 2302522004984615874003468288, 88558538653254456692441088, 2277219565369400314948485120
  ]
def negativeScales : Array ℕ := #[
    9, 8, 9, 8, 30, 31,
    34, 31, 26, 31, 31, 29,
    31, 23, 46, 52, 36, 35,
    41, 39, 51, 41, 36, 36,
    34, 36, 39, 34, 45, 35,
    39, 48, 30, 54, 30, 25,
    30, 29, 30, 34, 24, 49,
    30, 25, 24, 25, 29, 29,
    44, 13, 15, 17, 12, 12,
    14, 17, 17, 12, 21, 16,
    15, 17, 14, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9063395081288510, 8933690662845865, 9063395081288510, 8933690662845865, 30768453105011553, 31322210112956628,
    34249861646404394, 31857592586895327, 26945444125107445, 31857300986127060, 31366595706923218, 29771757635546713,
    31322210112956628, 23897845737110300, 46669724360218419, 52465658002633717, 36104459497931251, 35967564844525561,
    41396935550833730, 39796146199259207, 51465658266070844, 41396935550833730, 36104459497931251, 36101494072974085,
    34898268851166645, 36101494072974085, 39796146199259207, 34898268851166645, 45669709723992497, 35967564844525561,
    39344814982258931, 48248138602511040, 30573028272013463, 54613129136935813, 30553196105401011, 25657795912846312,
    30573028272013463, 29843385075537585, 30553196105401011, 34548109060783383, 24965467044725730, 49248139008777869,
    30573028272013463, 25657795912846312, 24965467044725730, 25657795912846312, 29581679153162096, 29843385075537585,
    44346282901642351, 13709406960819918, 15779796289046625, 17895273510052851, 12972441381715804, 12972441381715804,
    14194833787899984, 17895273510052851, 17895273510052851, 12972441381715804, 21520621078243513, 16879331965172975,
    15779796289046625, 17895273510052851, 14194833787899984, 16879331965172975
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
noncomputable def negativeCeiling : ℝ := 35909661933 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 20696810031802451470969733120, coefficient := (-20696810031802451470969733120) }, { argument := 18917271225329717325802242048, coefficient := (-18917271225329717325802242048) }, { argument := 134960605644752413891254812672, coefficient := (-134960605644752413891254812672) }, { argument := 198109128879163635831391911936, coefficient := (-198109128879163635831391911936) }, { argument := 1507354551793106610270773444608, coefficient := (-1507354551793106610270773444608) }, { argument := 287124777407842757443848241152, coefficient := (-287124777407842757443848241152) }, { argument := 9536008709794602301037477888, coefficient := (-9536008709794602301037477888) }, { argument := 287066748968501255243462344704, coefficient := (-287066748968501255243462344704) }, { argument := 204298831879495636409739378688, coefficient := (-204298831879495636409739378688) }, { argument := 135270090728360735254817800192, coefficient := (-135270090728360735254817800192) }, { argument := 198109128879163635831391911936, coefficient := (-198109128879163635831391911936) }, { argument := 9226523626186280937474490368, coefficient := (-9226523626186280937474490368) }, { argument := 252067410945074139824392241152, coefficient := (-252067410945074139824392241152) }, { argument := 14004466850604661440707572006912, coefficient := (-14004466850604661440707572006912) }, { argument := 85177526825592757665482670080, coefficient := (-85177526825592757665482670080) }, { argument := 77466801485654581764054581248, coefficient := (-77466801485654581764054581248) }, { argument := 3338251625980430182862530019328, coefficient := (-3338251625980430182862530019328) }, { argument := 1100610007675670807603293716480, coefficient := (-1100610007675670807603293716480) }, { argument := 14004469407830376029503218515968, coefficient := (-14004469407830376029503218515968) }, { argument := 3338251625980430182862530019328, coefficient := (-3338251625980430182862530019328) }, { argument := 85177526825592757665482670080, coefficient := (-85177526825592757665482670080) }, { argument := 85002626281384029581255639040, coefficient := (-85002626281384029581255639040) }, { argument := 73833839844634938967484006400, coefficient := (-73833839844634938967484006400) }, { argument := 85002626281384029581255639040, coefficient := (-85002626281384029581255639040) }, { argument := 1100610007675670807603293716480, coefficient := (-1100610007675670807603293716480) }, { argument := 73833839844634938967484006400, coefficient := (-73833839844634938967484006400) }, { argument := 252064853719359551028745732096, coefficient := (-252064853719359551028745732096) }, { argument := 77466801485654581764054581248, coefficient := (-77466801485654581764054581248) }, { argument := 12577352977681703640101814272, coefficient := (-12577352977681703640101814272) }, { argument := 1505555358180670572062924865536, coefficient := (-1505555358180670572062924865536) }, { argument := 29465803657967788753390927872, coefficient := (-29465803657967788753390927872) }, { argument := 15511714930734622454437902286848, coefficient := (-15511714930734622454437902286848) }, { argument := 29063520088474358940115664896, coefficient := (-29063520088474358940115664896) }, { argument := 976530730954752228790894592, coefficient := (-976530730954752228790894592) }, { argument := 29465803657967788753390927872, coefficient := (-29465803657967788753390927872) }, { argument := 17769442479379996009102835712, coefficient := (-17769442479379996009102835712) }, { argument := 29063520088474358940115664896, coefficient := (-29063520088474358940115664896) }, { argument := 463379528440040041087538036736, coefficient := (-463379528440040041087538036736) }, { argument := 19338560032520432321078231040, coefficient := (-19338560032520432321078231040) }, { argument := 1505555782149194967349924462592, coefficient := (-1505555782149194967349924462592) }, { argument := 29465803657967788753390927872, coefficient := (-29465803657967788753390927872) }, { argument := 976530730954752228790894592, coefficient := (-976530730954752228790894592) }, { argument := 19338560032520432321078231040, coefficient := (-19338560032520432321078231040) }, { argument := 976530730954752228790894592, coefficient := (-976530730954752228790894592) }, { argument := 29643021251582755310122565632, coefficient := (-29643021251582755310122565632) }, { argument := 17769442479379996009102835712, coefficient := (-17769442479379996009102835712) }, { argument := 12590156748099070375581712384, coefficient := (-12590156748099070375581712384) }, { argument := 63256099038038897637457920, coefficient := (-63256099038038897637457920) }, { argument := 1062702463839053480309293056, coefficient := (-1062702463839053480309293056) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 75907318845646677164949504, coefficient := (-75907318845646677164949504) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 1214517101530346834639192064, coefficient := (-1214517101530346834639192064) }, { argument := 28414639687887072818746097664, coefficient := (-28414639687887072818746097664) }, { argument := 2277219565369400314948485120, coefficient := (-2277219565369400314948485120) }, { argument := 1062702463839053480309293056, coefficient := (-1062702463839053480309293056) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2277219565369400314948485120, coefficient := (-2277219565369400314948485120) }] }

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
def constantNumerator : ℤ := (-43242010413312741720172388935532544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18753, 243789, 243789, 8037, 11153810674191, 6815,
    50991654961727, 168635, 5365, 815839856498539, 2755, 2755,
    93235, 5075, 168635, 93235, 22334259863687, 5365,
    5075, 6815, 1829057223, 2684878347, 20428461815, 3891264729,
    129236967, 3890478297, 2768764389, 916625763, 2684878347, 15630333,
    195192234221027, 10639059940354077, 133696378235, 242835447701, 10513087962825, 1715441782047,
    5319530949532753, 10513087962825, 133696378235, 266874076917, 231638994867, 266874076917,
    1715441782047, 231638994867, 97595137754799, 242835447701, 204298665288545, 24460651545281359,
    54378558303, 504578732085636625, 55751219259, 1777645203, 54378558303, 30963528753,
    55751219259, 870761676309, 1067356485, 3057582327429861, 54378558303, 1777645203,
    1067356485, 1777645203, 27366665739, 30963528753
  ]
def negativeCoefficients : Array ℕ := #[
    88558538653254456692441088, 2302522004984615874003468288, 2302522004984615874003468288, 75907318845646677164949504, 12558074399011912091575517184, 64365855161513264262676480,
    459291996569277241345058013184, 1592712543677445241223249920, 50670992361191293142958080, 459277009215102396239779463168, 52040478641223490254929920, 52040478641223490254929920,
    880579678060702742997893120, 47932019801126898919014400, 1592712543677445241223249920, 880579678060702742997893120, 12573070549962074748400697344, 50670992361191293142958080,
    47932019801126898919014400, 64365855161513264262676480, 134960601955403599149344489472, 198109054944613388403509035008, 1507354427683412482352910172160, 287124658315663017574983008256,
    9536005020445787559127154688, 287066629876321515374597111808, 204298752337135190574152810496, 135270086891437967923231064064, 198109054944613388403509035008, 9226520084411418785240580096,
    879067673303431774766882619392, 47914066382950992576790703112192, 308282859110364616548123934720, 279970209735314219406958002176, 12120765192164330727462351667200, 3955539440846156193254546079744,
    47914075204203054347522435710976, 12120765192164330727462351667200, 308282859110364616548123934720, 307684862299711049717872852992, 267061578487679343526718472192, 307684862299711049717872852992,
    3955539440846156193254546079744, 267061578487679343526718472192, 879058852051370004035150020608, 279970209735314219406958002176, 460039696432890473833729884160, 55080490592284337778686827692032,
    1003107348112734582038643867648, 568105147449987609582584725504000, 1028428473468040069626193772544, 32791766113598462845463298048, 1003107348112734582038643867648, 571176290525538052832753614848,
    1028428473468040069626193772544, 16062717792066440621132919865344, 630056061254694653560954552320, 55080506521870943560981203124224, 1003107348112734582038643867648, 32791766113598462845463298048,
    630056061254694653560954552320, 32791766113598462845463298048, 1009651758076176953693278568448, 571176290525538052832753614848
  ]
def negativeScales : Array ℕ := #[
    14, 17, 17, 12, 43, 12,
    45, 17, 12, 49, 11, 11,
    16, 12, 17, 16, 44, 12,
    12, 12, 30, 31, 34, 31,
    26, 31, 31, 29, 31, 23,
    47, 53, 36, 37, 43, 40,
    52, 43, 36, 37, 37, 37,
    40, 37, 46, 37, 47, 54,
    35, 58, 35, 30, 35, 34,
    35, 39, 29, 51, 35, 30,
    29, 30, 34, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14194833787899984, 17895273510052851, 17895273510052851, 12972441381715804, 43342601921396320, 12734497941852221,
    45535326395710335, 17363544471488155, 12389362455643889, 49535279317741428, 11427836603458541, 11427836603458541,
    16508584017343242, 12309192106959902, 17363544471488155, 16508584017343242, 44344323679415701, 12389362455643889,
    12309192106959902, 12734497941852221, 30768453065573338, 31322209574541112, 34249861527618507, 31857591988501343,
    26945443566948649, 31857300387612116, 31366595145219608, 29771757594624809, 31322209574541112, 23897845183304489,
    47471888984430122, 53240220199177424, 36960169440231450, 37821188077915647, 43257251721514961, 40641717303804933,
    52240220464785760, 43257251721514961, 36960169440231450, 37957368230205566, 37753087185781494, 37957368230205566,
    40641717303804933, 37753087185781494, 46471874507227918, 37821188077915647, 47537673107199544, 54441312350870463,
    35662318851705520, 58807857012068976, 35698284305539821, 30727320262119954, 35662318851705520, 34849850847934245,
    35698284305539821, 39663486957270599, 29991394975093575, 51441312768105895, 35662318851705520, 30727320262119954,
    29991394975093575, 30727320262119954, 34671700621288182, 34849850847934245
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
noncomputable def negativeCeiling : ℝ := 282467781197 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 88558538653254456692441088, coefficient := (-88558538653254456692441088) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 2302522004984615874003468288, coefficient := (-2302522004984615874003468288) }, { argument := 75907318845646677164949504, coefficient := (-75907318845646677164949504) }, { argument := 12558074399011912091575517184, coefficient := (-12558074399011912091575517184) }, { argument := 64365855161513264262676480, coefficient := (-64365855161513264262676480) }, { argument := 459291996569277241345058013184, coefficient := (-459291996569277241345058013184) }, { argument := 1592712543677445241223249920, coefficient := (-1592712543677445241223249920) }, { argument := 50670992361191293142958080, coefficient := (-50670992361191293142958080) }, { argument := 459277009215102396239779463168, coefficient := (-459277009215102396239779463168) }, { argument := 52040478641223490254929920, coefficient := (-52040478641223490254929920) }, { argument := 52040478641223490254929920, coefficient := (-52040478641223490254929920) }, { argument := 880579678060702742997893120, coefficient := (-880579678060702742997893120) }, { argument := 47932019801126898919014400, coefficient := (-47932019801126898919014400) }, { argument := 1592712543677445241223249920, coefficient := (-1592712543677445241223249920) }, { argument := 880579678060702742997893120, coefficient := (-880579678060702742997893120) }, { argument := 12573070549962074748400697344, coefficient := (-12573070549962074748400697344) }, { argument := 50670992361191293142958080, coefficient := (-50670992361191293142958080) }, { argument := 47932019801126898919014400, coefficient := (-47932019801126898919014400) }, { argument := 64365855161513264262676480, coefficient := (-64365855161513264262676480) }, { argument := 134960601955403599149344489472, coefficient := (-134960601955403599149344489472) }, { argument := 198109054944613388403509035008, coefficient := (-198109054944613388403509035008) }, { argument := 1507354427683412482352910172160, coefficient := (-1507354427683412482352910172160) }, { argument := 287124658315663017574983008256, coefficient := (-287124658315663017574983008256) }, { argument := 9536005020445787559127154688, coefficient := (-9536005020445787559127154688) }, { argument := 287066629876321515374597111808, coefficient := (-287066629876321515374597111808) }, { argument := 204298752337135190574152810496, coefficient := (-204298752337135190574152810496) }, { argument := 135270086891437967923231064064, coefficient := (-135270086891437967923231064064) }, { argument := 198109054944613388403509035008, coefficient := (-198109054944613388403509035008) }, { argument := 9226520084411418785240580096, coefficient := (-9226520084411418785240580096) }, { argument := 879067673303431774766882619392, coefficient := (-879067673303431774766882619392) }, { argument := 47914066382950992576790703112192, coefficient := (-47914066382950992576790703112192) }, { argument := 308282859110364616548123934720, coefficient := (-308282859110364616548123934720) }, { argument := 279970209735314219406958002176, coefficient := (-279970209735314219406958002176) }, { argument := 12120765192164330727462351667200, coefficient := (-12120765192164330727462351667200) }, { argument := 3955539440846156193254546079744, coefficient := (-3955539440846156193254546079744) }, { argument := 47914075204203054347522435710976, coefficient := (-47914075204203054347522435710976) }, { argument := 12120765192164330727462351667200, coefficient := (-12120765192164330727462351667200) }, { argument := 308282859110364616548123934720, coefficient := (-308282859110364616548123934720) }, { argument := 307684862299711049717872852992, coefficient := (-307684862299711049717872852992) }, { argument := 267061578487679343526718472192, coefficient := (-267061578487679343526718472192) }, { argument := 307684862299711049717872852992, coefficient := (-307684862299711049717872852992) }, { argument := 3955539440846156193254546079744, coefficient := (-3955539440846156193254546079744) }, { argument := 267061578487679343526718472192, coefficient := (-267061578487679343526718472192) }, { argument := 879058852051370004035150020608, coefficient := (-879058852051370004035150020608) }, { argument := 279970209735314219406958002176, coefficient := (-279970209735314219406958002176) }, { argument := 460039696432890473833729884160, coefficient := (-460039696432890473833729884160) }, { argument := 55080490592284337778686827692032, coefficient := (-55080490592284337778686827692032) }, { argument := 1003107348112734582038643867648, coefficient := (-1003107348112734582038643867648) }, { argument := 568105147449987609582584725504000, coefficient := (-568105147449987609582584725504000) }, { argument := 1028428473468040069626193772544, coefficient := (-1028428473468040069626193772544) }, { argument := 32791766113598462845463298048, coefficient := (-32791766113598462845463298048) }, { argument := 1003107348112734582038643867648, coefficient := (-1003107348112734582038643867648) }, { argument := 571176290525538052832753614848, coefficient := (-571176290525538052832753614848) }, { argument := 1028428473468040069626193772544, coefficient := (-1028428473468040069626193772544) }, { argument := 16062717792066440621132919865344, coefficient := (-16062717792066440621132919865344) }, { argument := 630056061254694653560954552320, coefficient := (-630056061254694653560954552320) }, { argument := 55080506521870943560981203124224, coefficient := (-55080506521870943560981203124224) }, { argument := 1003107348112734582038643867648, coefficient := (-1003107348112734582038643867648) }, { argument := 32791766113598462845463298048, coefficient := (-32791766113598462845463298048) }, { argument := 630056061254694653560954552320, coefficient := (-630056061254694653560954552320) }, { argument := 32791766113598462845463298048, coefficient := (-32791766113598462845463298048) }, { argument := 1009651758076176953693278568448, coefficient := (-1009651758076176953693278568448) }, { argument := 571176290525538052832753614848, coefficient := (-571176290525538052832753614848) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk10
