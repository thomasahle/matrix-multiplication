import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-292714702210281786981825975943168)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1014099, 477793, 516687, 516687, 25283403, 975549,
    12458083, 25283403, 74543, 1014099, 975549, 1223567,
    134912886925, 471844658069, 67456421359, 565, 4805, 29845,
    659395, 16515, 29845, 4185, 4185, 61935,
    16065, 659395, 61935, 565, 16515, 16065,
    4805, 106125819715, 368860825799, 53062892539, 4163, 4163,
    82901, 1500369, 1153477, 17734587, 1365143, 1153477,
    686309, 686309, 51433421, 1350193, 17734587, 51433421,
    82901, 1365143, 1350193, 1500369, 104440997905, 367935501867,
    26110240881, 74543, 1223567, 477793, 12458083, 1014099,
    477793, 516687, 516687, 25283403
  ]
def negativeCoefficients : Array ℕ := #[
    9577894255823248683127799808, 9025254595798945582349811712, 9759941483737873506115780608, 9759941483737873506115780608, 238794989800171672809794174976, 9213799799993999037151838208,
    235326534400032473011110019072, 238794989800171672809794174976, 11264619671441662821265309696, 9577894255823248683127799808, 9213799799993999037151838208, 11556263580690726370372747264,
    155543968584424412653866188800, 543999853121614719666926649344, 155543917617223458498981920768, 341521544041132741854494720, 363055535203018324028948480, 281878055362489122805514240,
    6227809693943659411370147840, 311959529858368762816757760, 281878055362489122805514240, 316209659692951443509084160, 316209659692951443509084160, 9359352579729007241928376320,
    303459270189203401432104960, 6227809693943659411370147840, 9359352579729007241928376320, 341521544041132741854494720, 311959529858368762816757760, 303459270189203401432104960,
    363055535203018324028948480, 122354739743452784129568931840, 425267578270707158396985933824, 122354699809710629062210224128, 40262065496445610034414485504, 40262065496445610034414485504,
    6263822460742023325769793536, 7085292277536646719627853824, 5447141123561029752158420992, 83749219236335732701425303552, 6446705547524116075960598528, 5447141123561029752158420992,
    6482005236983566673932976128, 6482005236983566673932976128, 242887463429723750396661334016, 6376106168605214880015843328, 83749219236335732701425303552, 242887463429723750396661334016,
    6263822460742023325769793536, 6446705547524116075960598528, 6376106168605214880015843328, 7085292277536646719627853824, 120412272447273152869071585280, 424200752410776994639031304192,
    120412232808678902981065703424, 11264619671441662821265309696, 11556263580690726370372747264, 9025254595798945582349811712, 235326534400032473011110019072, 9577894255823248683127799808,
    9025254595798945582349811712, 9759941483737873506115780608, 9759941483737873506115780608, 238794989800171672809794174976
  ]
def negativeScales : Array ℕ := #[
    19, 18, 18, 18, 24, 19,
    23, 24, 16, 19, 19, 20,
    36, 38, 35, 9, 12, 14,
    19, 14, 14, 12, 12, 15,
    13, 19, 15, 9, 14, 13,
    12, 36, 38, 35, 12, 12,
    16, 20, 20, 24, 20, 20,
    19, 19, 25, 20, 24, 25,
    16, 20, 20, 20, 36, 38,
    34, 16, 20, 18, 23, 19,
    18, 18, 18, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19951767080370542, 18866026194244076, 18978931076868829, 18978931076868829, 24591687319218963, 19895854817016187,
    23570578753509629, 24591687319218963, 16185785261374854, 19951767080370542, 19895854817016187, 20222661671903083,
    36973237220703773, 38779521014108729, 35973236747974683, 9142107057302551, 12230320715661113, 14865201635645939,
    19330783421950795, 14011489349172888, 14865201635645939, 12031011907437707, 12031011907437707, 15918467304844059,
    13971633375310864, 19330783421950795, 15918467304844059, 9142107057302551, 14011489349172888, 13971633375310864,
    12230320715661113, 36626984740959259, 38424285622095660, 35626984270097065, 12023407843140219, 12023407843140219,
    16339101884000748, 20516885929379953, 20137557806707222, 24080062397642820, 20380620652033502, 20137557806707222,
    19388498748206514, 19388498748206514, 25616202779326119, 20364734213816189, 24080062397642820, 25616202779326119,
    16339101884000748, 20380620652033502, 20364734213816189, 20516885929379953, 36603897191150715, 38420661931532529,
    34603896716228918, 16185785261374854, 20222661671903083, 18866026194244076, 23570578753509629, 19951767080370542,
    18866026194244076, 18978931076868829, 18978931076868829, 24591687319218963
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
noncomputable def negativeCeiling : ℝ := 402493451 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9577894255823248683127799808, coefficient := (-9577894255823248683127799808) }, { argument := 9025254595798945582349811712, coefficient := (-9025254595798945582349811712) }, { argument := 9759941483737873506115780608, coefficient := (-9759941483737873506115780608) }, { argument := 9759941483737873506115780608, coefficient := (-9759941483737873506115780608) }, { argument := 238794989800171672809794174976, coefficient := (-238794989800171672809794174976) }, { argument := 9213799799993999037151838208, coefficient := (-9213799799993999037151838208) }, { argument := 235326534400032473011110019072, coefficient := (-235326534400032473011110019072) }, { argument := 238794989800171672809794174976, coefficient := (-238794989800171672809794174976) }, { argument := 11264619671441662821265309696, coefficient := (-11264619671441662821265309696) }, { argument := 9577894255823248683127799808, coefficient := (-9577894255823248683127799808) }, { argument := 9213799799993999037151838208, coefficient := (-9213799799993999037151838208) }, { argument := 11556263580690726370372747264, coefficient := (-11556263580690726370372747264) }, { argument := 155543968584424412653866188800, coefficient := (-155543968584424412653866188800) }, { argument := 543999853121614719666926649344, coefficient := (-543999853121614719666926649344) }, { argument := 155543917617223458498981920768, coefficient := (-155543917617223458498981920768) }, { argument := 341521544041132741854494720, coefficient := (-341521544041132741854494720) }, { argument := 363055535203018324028948480, coefficient := (-363055535203018324028948480) }, { argument := 281878055362489122805514240, coefficient := (-281878055362489122805514240) }, { argument := 6227809693943659411370147840, coefficient := (-6227809693943659411370147840) }, { argument := 311959529858368762816757760, coefficient := (-311959529858368762816757760) }, { argument := 281878055362489122805514240, coefficient := (-281878055362489122805514240) }, { argument := 316209659692951443509084160, coefficient := (-316209659692951443509084160) }, { argument := 316209659692951443509084160, coefficient := (-316209659692951443509084160) }, { argument := 9359352579729007241928376320, coefficient := (-9359352579729007241928376320) }, { argument := 303459270189203401432104960, coefficient := (-303459270189203401432104960) }, { argument := 6227809693943659411370147840, coefficient := (-6227809693943659411370147840) }, { argument := 9359352579729007241928376320, coefficient := (-9359352579729007241928376320) }, { argument := 341521544041132741854494720, coefficient := (-341521544041132741854494720) }, { argument := 311959529858368762816757760, coefficient := (-311959529858368762816757760) }, { argument := 303459270189203401432104960, coefficient := (-303459270189203401432104960) }, { argument := 363055535203018324028948480, coefficient := (-363055535203018324028948480) }, { argument := 122354739743452784129568931840, coefficient := (-122354739743452784129568931840) }, { argument := 425267578270707158396985933824, coefficient := (-425267578270707158396985933824) }, { argument := 122354699809710629062210224128, coefficient := (-122354699809710629062210224128) }, { argument := 40262065496445610034414485504, coefficient := (-40262065496445610034414485504) }, { argument := 40262065496445610034414485504, coefficient := (-40262065496445610034414485504) }, { argument := 6263822460742023325769793536, coefficient := (-6263822460742023325769793536) }, { argument := 7085292277536646719627853824, coefficient := (-7085292277536646719627853824) }, { argument := 5447141123561029752158420992, coefficient := (-5447141123561029752158420992) }, { argument := 83749219236335732701425303552, coefficient := (-83749219236335732701425303552) }, { argument := 6446705547524116075960598528, coefficient := (-6446705547524116075960598528) }, { argument := 5447141123561029752158420992, coefficient := (-5447141123561029752158420992) }, { argument := 6482005236983566673932976128, coefficient := (-6482005236983566673932976128) }, { argument := 6482005236983566673932976128, coefficient := (-6482005236983566673932976128) }, { argument := 242887463429723750396661334016, coefficient := (-242887463429723750396661334016) }, { argument := 6376106168605214880015843328, coefficient := (-6376106168605214880015843328) }, { argument := 83749219236335732701425303552, coefficient := (-83749219236335732701425303552) }, { argument := 242887463429723750396661334016, coefficient := (-242887463429723750396661334016) }, { argument := 6263822460742023325769793536, coefficient := (-6263822460742023325769793536) }, { argument := 6446705547524116075960598528, coefficient := (-6446705547524116075960598528) }, { argument := 6376106168605214880015843328, coefficient := (-6376106168605214880015843328) }, { argument := 7085292277536646719627853824, coefficient := (-7085292277536646719627853824) }, { argument := 120412272447273152869071585280, coefficient := (-120412272447273152869071585280) }, { argument := 424200752410776994639031304192, coefficient := (-424200752410776994639031304192) }, { argument := 120412232808678902981065703424, coefficient := (-120412232808678902981065703424) }, { argument := 11264619671441662821265309696, coefficient := (-11264619671441662821265309696) }, { argument := 11556263580690726370372747264, coefficient := (-11556263580690726370372747264) }, { argument := 9025254595798945582349811712, coefficient := (-9025254595798945582349811712) }, { argument := 235326534400032473011110019072, coefficient := (-235326534400032473011110019072) }, { argument := 9577894255823248683127799808, coefficient := (-9577894255823248683127799808) }, { argument := 9025254595798945582349811712, coefficient := (-9025254595798945582349811712) }, { argument := 9759941483737873506115780608, coefficient := (-9759941483737873506115780608) }, { argument := 9759941483737873506115780608, coefficient := (-9759941483737873506115780608) }, { argument := 238794989800171672809794174976, coefficient := (-238794989800171672809794174976) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10284489951858419644812363548327936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    975549, 12458083, 25283403, 74543, 1014099, 975549,
    1223567, 1910423661295, 6701168868347, 955211517067, 114255, 114255,
    1707845415, 95085608445, 27325517715, 21213, 21213, 3729,
    218286531447479, 2657, 16048096023123749, 1273, 2329, 32095117578809345,
    1177, 1177, 76213, 2279, 1273, 76213,
    874221055473369, 2329, 2279, 2657, 8045515488049385, 14036200718277399,
    8045515470967017, 16583725623162955, 16583720906377141, 134912886925, 471844658069, 67456421359,
    114255, 114255, 71153565, 1015, 1015, 4353,
    289, 9857, 30599, 667169, 16983, 30599,
    2151, 2151, 257763, 16533, 667169, 257763,
    289, 16983, 16533, 9857
  ]
def negativeCoefficients : Array ℕ := #[
    9213799799993999037151838208, 235326534400032473011110019072, 238794989800171672809794174976, 11264619671441662821265309696, 9577894255823248683127799808, 9213799799993999037151838208,
    11556263580690726370372747264, 2202568522016752809415718993920, 7725921694319185297309719068672, 2202567798949349058680962678784, 1105006556160555650848433111040, 1105006556160555650848433111040,
    126016749151853119076365762560, 438504971019467660903873249280, 126016707992555404611928719360, 820638189167524117857347567616, 820638189167524117857347567616, 72129350101487235079669284864,
    491537570843432240622749089792, 401514487839508714649288704, 18068549817436513688856219877376, 6155850273477691757603848192, 351948529235308918486335488, 18067944946042252741074107760640,
    355726422421604634657292288, 355726422421604634657292288, 11516982936286216661485223936, 344392742862717486144421888, 6155850273477691757603848192, 11516982936286216661485223936,
    492142702458663292625253040128, 351948529235308918486335488, 344392742862717486144421888, 401514487839508714649288704, 18116890276991382274919869972480, 63213428324531582440249076219904,
    18116890238525309195217027465216, 18671615134222807676674291793920, 18671609823594099097463878057984, 155543968584424412653866188800, 543999853121614719666926649344, 155543917617223458498981920768,
    1105006556160555650848433111040, 1105006556160555650848433111040, 672026420985373374479314452480, 39265910621083155594456596480, 39265910621083155594456596480, 84199265484519692759935746048,
    349379561868627831490084864, 372386931373168742971211776, 288999384018656547787767808, 6301233048019316655152693248, 320799799914300738656796672, 288999384018656547787767808,
    325049929748883419349123072, 325049929748883419349123072, 9738010813791426873743376384, 312299540245135377272143872, 6301233048019316655152693248, 9738010813791426873743376384,
    349379561868627831490084864, 320799799914300738656796672, 312299540245135377272143872, 372386931373168742971211776
  ]
def negativeScales : Array ℕ := #[
    19, 23, 24, 16, 19, 19,
    20, 40, 42, 39, 16, 16,
    30, 36, 34, 14, 14, 11,
    47, 11, 53, 10, 11, 54,
    10, 10, 16, 11, 10, 16,
    49, 11, 11, 11, 52, 53,
    52, 53, 53, 36, 38, 35,
    16, 16, 26, 9, 9, 12,
    8, 13, 14, 19, 14, 14,
    11, 11, 17, 14, 19, 17,
    8, 14, 14, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19895854817016187, 23570578753509629, 24591687319218963, 16185785261374854, 19951767080370542, 19895854817016187,
    20222661671903083, 40797029749387513, 42607549901910606, 39797029275774124, 16801897776648667, 16801897776648667,
    30669530249877639, 36468507949305510, 34669529778667861, 14372661044692482, 14372661044692482, 11864573084055395,
    47633216445419849, 11375582512490509, 53833251662846701, 10314016703901359, 11185494924210867, 54833203365689602,
    10200898605038445, 10200898605038445, 16217749485350390, 11154185209265298, 10314016703901359, 16217749485350390,
    49634991454057357, 11185494924210867, 11154185209265298, 11375582512490509, 52837106284172102, 53640002001816000,
    52837106281108949, 53880617673717028, 53880617263381920, 36973237220703773, 38779521014108729, 35973236747974683,
    16801897776648667, 16801897776648667, 26084432705980495, 9987264031369531, 9987264031369531, 12087794304787901,
    8174925682500679, 13266932910607358, 14901196889262501, 19347692729968054, 14051803709042758, 14901196889262501,
    11070791809423061, 11070791809423061, 17975685680621011, 14013060912553662, 19347692729968054, 17975685680621011,
    8174925682500679, 14051803709042758, 14013060912553662, 13266932910607358
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
noncomputable def negativeCeiling : ℝ := 60327108419 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9213799799993999037151838208, coefficient := (-9213799799993999037151838208) }, { argument := 235326534400032473011110019072, coefficient := (-235326534400032473011110019072) }, { argument := 238794989800171672809794174976, coefficient := (-238794989800171672809794174976) }, { argument := 11264619671441662821265309696, coefficient := (-11264619671441662821265309696) }, { argument := 9577894255823248683127799808, coefficient := (-9577894255823248683127799808) }, { argument := 9213799799993999037151838208, coefficient := (-9213799799993999037151838208) }, { argument := 11556263580690726370372747264, coefficient := (-11556263580690726370372747264) }, { argument := 2202568522016752809415718993920, coefficient := (-2202568522016752809415718993920) }, { argument := 7725921694319185297309719068672, coefficient := (-7725921694319185297309719068672) }, { argument := 2202567798949349058680962678784, coefficient := (-2202567798949349058680962678784) }, { argument := 1105006556160555650848433111040, coefficient := (-1105006556160555650848433111040) }, { argument := 1105006556160555650848433111040, coefficient := (-1105006556160555650848433111040) }, { argument := 126016749151853119076365762560, coefficient := (-126016749151853119076365762560) }, { argument := 438504971019467660903873249280, coefficient := (-438504971019467660903873249280) }, { argument := 126016707992555404611928719360, coefficient := (-126016707992555404611928719360) }, { argument := 820638189167524117857347567616, coefficient := (-820638189167524117857347567616) }, { argument := 820638189167524117857347567616, coefficient := (-820638189167524117857347567616) }, { argument := 72129350101487235079669284864, coefficient := (-72129350101487235079669284864) }, { argument := 491537570843432240622749089792, coefficient := (-491537570843432240622749089792) }, { argument := 401514487839508714649288704, coefficient := (-401514487839508714649288704) }, { argument := 18068549817436513688856219877376, coefficient := (-18068549817436513688856219877376) }, { argument := 6155850273477691757603848192, coefficient := (-6155850273477691757603848192) }, { argument := 351948529235308918486335488, coefficient := (-351948529235308918486335488) }, { argument := 18067944946042252741074107760640, coefficient := (-18067944946042252741074107760640) }, { argument := 355726422421604634657292288, coefficient := (-355726422421604634657292288) }, { argument := 355726422421604634657292288, coefficient := (-355726422421604634657292288) }, { argument := 11516982936286216661485223936, coefficient := (-11516982936286216661485223936) }, { argument := 344392742862717486144421888, coefficient := (-344392742862717486144421888) }, { argument := 6155850273477691757603848192, coefficient := (-6155850273477691757603848192) }, { argument := 11516982936286216661485223936, coefficient := (-11516982936286216661485223936) }, { argument := 492142702458663292625253040128, coefficient := (-492142702458663292625253040128) }, { argument := 351948529235308918486335488, coefficient := (-351948529235308918486335488) }, { argument := 344392742862717486144421888, coefficient := (-344392742862717486144421888) }, { argument := 401514487839508714649288704, coefficient := (-401514487839508714649288704) }, { argument := 18116890276991382274919869972480, coefficient := (-18116890276991382274919869972480) }, { argument := 63213428324531582440249076219904, coefficient := (-63213428324531582440249076219904) }, { argument := 18116890238525309195217027465216, coefficient := (-18116890238525309195217027465216) }, { argument := 18671615134222807676674291793920, coefficient := (-18671615134222807676674291793920) }, { argument := 18671609823594099097463878057984, coefficient := (-18671609823594099097463878057984) }, { argument := 155543968584424412653866188800, coefficient := (-155543968584424412653866188800) }, { argument := 543999853121614719666926649344, coefficient := (-543999853121614719666926649344) }, { argument := 155543917617223458498981920768, coefficient := (-155543917617223458498981920768) }, { argument := 1105006556160555650848433111040, coefficient := (-1105006556160555650848433111040) }, { argument := 1105006556160555650848433111040, coefficient := (-1105006556160555650848433111040) }, { argument := 672026420985373374479314452480, coefficient := (-672026420985373374479314452480) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 39265910621083155594456596480, coefficient := (-39265910621083155594456596480) }, { argument := 84199265484519692759935746048, coefficient := (-84199265484519692759935746048) }, { argument := 349379561868627831490084864, coefficient := (-349379561868627831490084864) }, { argument := 372386931373168742971211776, coefficient := (-372386931373168742971211776) }, { argument := 288999384018656547787767808, coefficient := (-288999384018656547787767808) }, { argument := 6301233048019316655152693248, coefficient := (-6301233048019316655152693248) }, { argument := 320799799914300738656796672, coefficient := (-320799799914300738656796672) }, { argument := 288999384018656547787767808, coefficient := (-288999384018656547787767808) }, { argument := 325049929748883419349123072, coefficient := (-325049929748883419349123072) }, { argument := 325049929748883419349123072, coefficient := (-325049929748883419349123072) }, { argument := 9738010813791426873743376384, coefficient := (-9738010813791426873743376384) }, { argument := 312299540245135377272143872, coefficient := (-312299540245135377272143872) }, { argument := 6301233048019316655152693248, coefficient := (-6301233048019316655152693248) }, { argument := 9738010813791426873743376384, coefficient := (-9738010813791426873743376384) }, { argument := 349379561868627831490084864, coefficient := (-349379561868627831490084864) }, { argument := 320799799914300738656796672, coefficient := (-320799799914300738656796672) }, { argument := 312299540245135377272143872, coefficient := (-312299540245135377272143872) }, { argument := 372386931373168742971211776, coefficient := (-372386931373168742971211776) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
