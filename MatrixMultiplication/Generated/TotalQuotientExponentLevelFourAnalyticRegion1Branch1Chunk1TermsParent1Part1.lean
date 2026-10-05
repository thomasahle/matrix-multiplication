import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 1, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1

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
def constantNumerator : ℤ := (-2599301472648479539946043738161152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35954555, 8747897235, 87434827095, 174869611455, 8747897235, 218567367,
    147585081, 3829553, 25611060459, 237726867, 6994455025, 237726867,
    247742621, 147585081, 7364525, 6712867255, 6038342025, 165014265,
    13379535, 2867680335, 5186799735, 6038342025, 2867680335, 84737055,
    84737055, 165014265, 165014265, 5186799735, 165014265, 6712867255,
    13379535, 6988097007, 6476826789, 22370707051, 15904519955, 871585989,
    1452643315, 44450885439, 1452643315, 871585989, 712085753013, 45613000091,
    6476826789, 44450885439, 1452643315, 45613000091, 1452643315, 44450885439,
    1452643315, 6988097007, 106723187915, 7490786275, 31360281975, 84538873675,
    7490786275, 62720561175, 7490786275, 7490786275, 310546596715, 1926202185,
    84538873675, 310546596715, 106723187915, 7490786275
  ]
def negativeCoefficients : Array ℕ := #[
    82905559296139265950351360, 20171277684644552846837022720, 806443939275255290397468917760, 806443742194853292903046840320, 20171277684644552846837022720, 8063712563827101238919430144,
    170154013644043384107565056, 8830348013463329314963456, 29527542358967204927697321984, 274080417187111798352904192, 8064057611327921480689254400, 274080417187111798352904192,
    285627795358563844380164096, 170154013644043384107565056, 8490719243714739725926400, 7739409015860634713986170880, 6961734372793755197924966400, 6087951829932574966787604480,
    7897883455047664821778513920, 105798730449909343341741342720, 191359134546259045577675243520, 6961734372793755197924966400, 105798730449909343341741342720, 6252491068579401317241323520,
    6252491068579401317241323520, 6087951829932574966787604480, 6087951829932574966787604480, 191359134546259045577675243520, 6087951829932574966787604480, 7739409015860634713986170880,
    7897883455047664821778513920, 32226909262596176258770403328, 477905464745716058046748164096, 825333415435453460124199288832, 146693304612545777275387248640, 514493557674048910207293063168,
    26796539462190047406629847040, 819974107543015450642873319424, 857489262790081517012155105280, 514493557674048910207293063168, 13135663644365561238729951019008, 841411339112767488568177197056,
    477905464745716058046748164096, 819974107543015450642873319424, 26796539462190047406629847040, 841411339112767488568177197056, 26796539462190047406629847040, 819974107543015450642873319424,
    857489262790081517012155105280, 32226909262596176258770403328, 123043458387401068015297495040, 138180617325781097581536870400, 144623773918047930732144230400, 1559466966962386672705916108800,
    138180617325781097581536870400, 144623767519333580164143513600, 138180617325781097581536870400, 138180617325781097581536870400, 5728573592563096359737428541440, 142128634963660557512437923840,
    1559466966962386672705916108800, 5728573592563096359737428541440, 123043458387401068015297495040, 138180617325781097581536870400
  ]
def negativeScales : Array ℕ := #[
    25, 33, 36, 37, 33, 27,
    27, 21, 34, 27, 32, 27,
    27, 27, 22, 32, 32, 27,
    23, 31, 32, 32, 31, 26,
    26, 27, 27, 32, 27, 32,
    23, 32, 32, 34, 33, 29,
    30, 35, 30, 29, 39, 35,
    32, 35, 30, 35, 30, 35,
    30, 32, 36, 32, 34, 36,
    32, 35, 32, 32, 38, 30,
    36, 38, 36, 32
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    25099671218176001, 33026289126564003, 36347488998269186, 37347488645700409, 33026289126564003, 27703502776007649,
    27136971649500192, 21868744576912816, 34576047939698087, 27824729720643549, 32703564507829704, 27824729720643549,
    27884266849845248, 27136971649500192, 22812161046905850, 32644281967825033, 32491505330579042, 27298015505722659,
    23673524640853201, 31417237067421670, 32272197521566928, 32491505330579042, 31417237067421670, 26336489653537295,
    26336489653537295, 27298015505722659, 27298015505722659, 32272197521566928, 27298015505722659, 32644281967825033,
    23673524640853201, 32702252489584919, 32592640016322846, 34380891803967625, 33888717780208668, 29699067764064693,
    30436033358160111, 35371493105965375, 30436033358160111, 29699067764064693, 39373260032139563, 35408726012164357,
    32592640016322846, 35371493105965375, 30436033358160111, 35408726012164357, 30436033358160111, 35371493105965375,
    30436033358160111, 32702252489584919, 36635082710617431, 32802470014672334, 34868219482775362, 36298895840112491,
    32802470014672334, 35868219418944957, 32802470014672334, 32802470014672334, 38176018801114770, 30843112000008174,
    36298895840112491, 38176018801114770, 36635082710617431, 32802470014672334
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
noncomputable def negativeCeiling : ℝ := 4502247137 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 20171277684644552846837022720, coefficient := (-20171277684644552846837022720) }, { argument := 806443939275255290397468917760, coefficient := (-806443939275255290397468917760) }, { argument := 806443742194853292903046840320, coefficient := (-806443742194853292903046840320) }, { argument := 20171277684644552846837022720, coefficient := (-20171277684644552846837022720) }, { argument := 8063712563827101238919430144, coefficient := (-8063712563827101238919430144) }, { argument := 170154013644043384107565056, coefficient := (-170154013644043384107565056) }, { argument := 8830348013463329314963456, coefficient := (-8830348013463329314963456) }, { argument := 29527542358967204927697321984, coefficient := (-29527542358967204927697321984) }, { argument := 274080417187111798352904192, coefficient := (-274080417187111798352904192) }, { argument := 8064057611327921480689254400, coefficient := (-8064057611327921480689254400) }, { argument := 274080417187111798352904192, coefficient := (-274080417187111798352904192) }, { argument := 285627795358563844380164096, coefficient := (-285627795358563844380164096) }, { argument := 170154013644043384107565056, coefficient := (-170154013644043384107565056) }, { argument := 8490719243714739725926400, coefficient := (-8490719243714739725926400) }, { argument := 7739409015860634713986170880, coefficient := (-7739409015860634713986170880) }, { argument := 6961734372793755197924966400, coefficient := (-6961734372793755197924966400) }, { argument := 6087951829932574966787604480, coefficient := (-6087951829932574966787604480) }, { argument := 7897883455047664821778513920, coefficient := (-7897883455047664821778513920) }, { argument := 105798730449909343341741342720, coefficient := (-105798730449909343341741342720) }, { argument := 191359134546259045577675243520, coefficient := (-191359134546259045577675243520) }, { argument := 6961734372793755197924966400, coefficient := (-6961734372793755197924966400) }, { argument := 105798730449909343341741342720, coefficient := (-105798730449909343341741342720) }, { argument := 6252491068579401317241323520, coefficient := (-6252491068579401317241323520) }, { argument := 6252491068579401317241323520, coefficient := (-6252491068579401317241323520) }, { argument := 6087951829932574966787604480, coefficient := (-6087951829932574966787604480) }, { argument := 6087951829932574966787604480, coefficient := (-6087951829932574966787604480) }, { argument := 191359134546259045577675243520, coefficient := (-191359134546259045577675243520) }, { argument := 6087951829932574966787604480, coefficient := (-6087951829932574966787604480) }, { argument := 7739409015860634713986170880, coefficient := (-7739409015860634713986170880) }, { argument := 7897883455047664821778513920, coefficient := (-7897883455047664821778513920) }, { argument := 32226909262596176258770403328, coefficient := (-32226909262596176258770403328) }, { argument := 477905464745716058046748164096, coefficient := (-477905464745716058046748164096) }, { argument := 825333415435453460124199288832, coefficient := (-825333415435453460124199288832) }, { argument := 146693304612545777275387248640, coefficient := (-146693304612545777275387248640) }, { argument := 514493557674048910207293063168, coefficient := (-514493557674048910207293063168) }, { argument := 26796539462190047406629847040, coefficient := (-26796539462190047406629847040) }, { argument := 819974107543015450642873319424, coefficient := (-819974107543015450642873319424) }, { argument := 857489262790081517012155105280, coefficient := (-857489262790081517012155105280) }, { argument := 514493557674048910207293063168, coefficient := (-514493557674048910207293063168) }, { argument := 13135663644365561238729951019008, coefficient := (-13135663644365561238729951019008) }, { argument := 841411339112767488568177197056, coefficient := (-841411339112767488568177197056) }, { argument := 477905464745716058046748164096, coefficient := (-477905464745716058046748164096) }, { argument := 819974107543015450642873319424, coefficient := (-819974107543015450642873319424) }, { argument := 26796539462190047406629847040, coefficient := (-26796539462190047406629847040) }, { argument := 841411339112767488568177197056, coefficient := (-841411339112767488568177197056) }, { argument := 26796539462190047406629847040, coefficient := (-26796539462190047406629847040) }, { argument := 819974107543015450642873319424, coefficient := (-819974107543015450642873319424) }, { argument := 857489262790081517012155105280, coefficient := (-857489262790081517012155105280) }, { argument := 32226909262596176258770403328, coefficient := (-32226909262596176258770403328) }, { argument := 123043458387401068015297495040, coefficient := (-123043458387401068015297495040) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }, { argument := 144623773918047930732144230400, coefficient := (-144623773918047930732144230400) }, { argument := 1559466966962386672705916108800, coefficient := (-1559466966962386672705916108800) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }, { argument := 144623767519333580164143513600, coefficient := (-144623767519333580164143513600) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }, { argument := 5728573592563096359737428541440, coefficient := (-5728573592563096359737428541440) }, { argument := 142128634963660557512437923840, coefficient := (-142128634963660557512437923840) }, { argument := 1559466966962386672705916108800, coefficient := (-1559466966962386672705916108800) }, { argument := 5728573592563096359737428541440, coefficient := (-5728573592563096359737428541440) }, { argument := 123043458387401068015297495040, coefficient := (-123043458387401068015297495040) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }] }

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

namespace Parent1

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-802817937758729957162839313481728)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1926202185, 7490786275, 35954555, 1473064775, 30331544425, 1473064775,
    35954555, 340827165, 3406551705, 6813101745, 340827165, 412835325,
    29271263175, 759533775, 50445265325, 47149519725, 6663794375, 47149519725,
    49135992675, 29271263175, 1460641875, 568045275, 5677586175, 11355169575,
    568045275, 687558975, 5009225575, 1375118875, 169804905, 33678228375,
    33678228375, 169804905, 35954555, 1473064775, 30331544425, 1473064775,
    35954555, 176959015, 35097137625, 35097137625, 176959015, 1490573123,
    61069056815, 1257459170305, 61069056815, 1490573123, 17382185415, 173734136955,
    347468188995, 17382185415, 9245457, 378788085, 7799539995, 378788085,
    9245457, 568045275, 5677586175, 11355169575, 568045275, 55748025,
    406153425, 111496125, 105417915, 20908045125
  ]
def negativeCoefficients : Array ℕ := #[
    142128634963660557512437923840, 138180617325781097581536870400, 82905559296139265950351360, 13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200,
    82905559296139265950351360, 12574302972245955021404897280, 502718299807951349858162442240, 502718176952635818952548679680, 12574302972245955021404897280, 7615467584861706696995635200,
    33747468781463992741448908800, 1751365645345436749057228800, 58159431198790605515993907200, 54359695222837209864968601600, 7682831837215643465154560000, 54359695222837209864968601600,
    56649942605212011767581900800, 33747468781463992741448908800, 1684005428216766104862720000, 654911613137810157364838400, 26183244781664132805112627200, 26183238382949782237111910400,
    654911613137810157364838400, 6341612223703531878403276800, 23100975547376392769162444800, 6341616489513098923737088000, 195771726562222713109217280, 38828353730598007046406144000,
    38828353730598007046406144000, 195771726562222713109217280, 82905559296139265950351360, 13586624454210772033286963200, 139879559342081684846883635200, 13586624454210772033286963200,
    82905559296139265950351360, 204019853827545603128688640, 40464244718008579833987072000, 40464244718008579833987072000, 204019853827545603128688640, 3437027615391373568398852096,
    563262630944566577722839531520, 5799006874438872134652232990720, 563262630944566577722839531520, 3437027615391373568398852096, 20040295362016990815364055040, 801207290318922463836446392320,
    801207094518263336455624458240, 20040295362016990815364055040, 85274289561743244977504256, 13974813724331079805666590720, 143876118180426875842508881920, 13974813724331079805666590720,
    85274289561743244977504256, 20957171620409925035674828800, 837863833013252249763604070400, 837863628254393031587581132800, 20957171620409925035674828800, 8226956398318095409820467200,
    29968833142542347376210739200, 8226961932341317522685952000, 121538581174316702933975040, 24105334843902851958177792000
  ]
def negativeScales : Array ℕ := #[
    30, 32, 25, 30, 34, 30,
    25, 28, 31, 32, 28, 28,
    34, 29, 35, 35, 32, 35,
    35, 34, 30, 29, 32, 33,
    29, 29, 32, 30, 27, 34,
    34, 27, 25, 30, 34, 30,
    25, 27, 35, 35, 27, 30,
    35, 40, 35, 30, 34, 37,
    38, 34, 23, 28, 32, 28,
    23, 29, 32, 33, 29, 25,
    28, 26, 26, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30843112000008174, 32802470014672334, 25099671218176001, 30456173725308212, 34820099908982713, 30456173725308212,
    25099671218176001, 28344465086590259, 31665664958327022, 32665664605758245, 28344465086590259, 28620991181957953,
    34768765954505907, 29500538879115002, 35553999816567726, 35456524024251474, 32633696738085368, 35456524024251474,
    35516061151229238, 34768765954505907, 30443955350748396, 29081430680756464, 32402630552461654, 33402630199892877,
    29081430680756464, 29356908224319502, 32221940434359524, 30356909194776229, 27339302892412522, 34971097211901790,
    34971097211901790, 27339302892412522, 25099671218176001, 30456173725308212, 34820099908982713, 30456173725308212,
    25099671218176001, 27398840019389892, 35030634324058537, 35030634324058537, 27398840019389892, 30473220005297887,
    35829722513600130, 40193648695136562, 35829722513600130, 30473220005297887, 34016890428561754, 37338090300266936,
    38338089947698159, 34016890428561754, 23140313202673347, 28496815709805743, 32860741894635460, 28496815709805743,
    23140313202673347, 29081430680756464, 32402630552461654, 33402630199892877, 29081430680756464, 25732417359564092,
    28597449569456999, 26732418330020822, 26651544822352109, 34283339126998601
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
noncomputable def negativeCeiling : ℝ := 5685550027 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 142128634963660557512437923840, coefficient := (-142128634963660557512437923840) }, { argument := 138180617325781097581536870400, coefficient := (-138180617325781097581536870400) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 12574302972245955021404897280, coefficient := (-12574302972245955021404897280) }, { argument := 502718299807951349858162442240, coefficient := (-502718299807951349858162442240) }, { argument := 502718176952635818952548679680, coefficient := (-502718176952635818952548679680) }, { argument := 12574302972245955021404897280, coefficient := (-12574302972245955021404897280) }, { argument := 7615467584861706696995635200, coefficient := (-7615467584861706696995635200) }, { argument := 33747468781463992741448908800, coefficient := (-33747468781463992741448908800) }, { argument := 1751365645345436749057228800, coefficient := (-1751365645345436749057228800) }, { argument := 58159431198790605515993907200, coefficient := (-58159431198790605515993907200) }, { argument := 54359695222837209864968601600, coefficient := (-54359695222837209864968601600) }, { argument := 7682831837215643465154560000, coefficient := (-7682831837215643465154560000) }, { argument := 54359695222837209864968601600, coefficient := (-54359695222837209864968601600) }, { argument := 56649942605212011767581900800, coefficient := (-56649942605212011767581900800) }, { argument := 33747468781463992741448908800, coefficient := (-33747468781463992741448908800) }, { argument := 1684005428216766104862720000, coefficient := (-1684005428216766104862720000) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 26183244781664132805112627200, coefficient := (-26183244781664132805112627200) }, { argument := 26183238382949782237111910400, coefficient := (-26183238382949782237111910400) }, { argument := 654911613137810157364838400, coefficient := (-654911613137810157364838400) }, { argument := 6341612223703531878403276800, coefficient := (-6341612223703531878403276800) }, { argument := 23100975547376392769162444800, coefficient := (-23100975547376392769162444800) }, { argument := 6341616489513098923737088000, coefficient := (-6341616489513098923737088000) }, { argument := 195771726562222713109217280, coefficient := (-195771726562222713109217280) }, { argument := 38828353730598007046406144000, coefficient := (-38828353730598007046406144000) }, { argument := 38828353730598007046406144000, coefficient := (-38828353730598007046406144000) }, { argument := 195771726562222713109217280, coefficient := (-195771726562222713109217280) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 139879559342081684846883635200, coefficient := (-139879559342081684846883635200) }, { argument := 13586624454210772033286963200, coefficient := (-13586624454210772033286963200) }, { argument := 82905559296139265950351360, coefficient := (-82905559296139265950351360) }, { argument := 204019853827545603128688640, coefficient := (-204019853827545603128688640) }, { argument := 40464244718008579833987072000, coefficient := (-40464244718008579833987072000) }, { argument := 40464244718008579833987072000, coefficient := (-40464244718008579833987072000) }, { argument := 204019853827545603128688640, coefficient := (-204019853827545603128688640) }, { argument := 3437027615391373568398852096, coefficient := (-3437027615391373568398852096) }, { argument := 563262630944566577722839531520, coefficient := (-563262630944566577722839531520) }, { argument := 5799006874438872134652232990720, coefficient := (-5799006874438872134652232990720) }, { argument := 563262630944566577722839531520, coefficient := (-563262630944566577722839531520) }, { argument := 3437027615391373568398852096, coefficient := (-3437027615391373568398852096) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 801207290318922463836446392320, coefficient := (-801207290318922463836446392320) }, { argument := 801207094518263336455624458240, coefficient := (-801207094518263336455624458240) }, { argument := 20040295362016990815364055040, coefficient := (-20040295362016990815364055040) }, { argument := 85274289561743244977504256, coefficient := (-85274289561743244977504256) }, { argument := 13974813724331079805666590720, coefficient := (-13974813724331079805666590720) }, { argument := 143876118180426875842508881920, coefficient := (-143876118180426875842508881920) }, { argument := 13974813724331079805666590720, coefficient := (-13974813724331079805666590720) }, { argument := 85274289561743244977504256, coefficient := (-85274289561743244977504256) }, { argument := 20957171620409925035674828800, coefficient := (-20957171620409925035674828800) }, { argument := 837863833013252249763604070400, coefficient := (-837863833013252249763604070400) }, { argument := 837863628254393031587581132800, coefficient := (-837863628254393031587581132800) }, { argument := 20957171620409925035674828800, coefficient := (-20957171620409925035674828800) }, { argument := 8226956398318095409820467200, coefficient := (-8226956398318095409820467200) }, { argument := 29968833142542347376210739200, coefficient := (-29968833142542347376210739200) }, { argument := 8226961932341317522685952000, coefficient := (-8226961932341317522685952000) }, { argument := 121538581174316702933975040, coefficient := (-121538581174316702933975040) }, { argument := 24105334843902851958177792000, coefficient := (-24105334843902851958177792000) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk1
