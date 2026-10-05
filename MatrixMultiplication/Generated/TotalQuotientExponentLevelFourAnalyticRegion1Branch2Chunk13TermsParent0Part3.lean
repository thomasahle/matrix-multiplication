import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
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

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-377597493524777504321884280324096)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4803116545, 8383776017, 4803114973, 565, 4805, 29845,
    659395, 16515, 29845, 4185, 4185, 61935,
    16065, 659395, 61935, 565, 16515, 16065,
    4805, 1707845415, 95085608445, 27325517715, 4011, 4011,
    4803116545, 8383776017, 4803114973, 3711, 3711, 21,
    2647, 45543, 17647, 367557, 39571, 17647,
    20023, 20023, 1247587, 38621, 367557, 1247587,
    2647, 39571, 38621, 45543, 67674527305, 118351254791,
    67674505129, 4011, 4011, 106125819715, 368860825799, 53062892539,
    21213, 21213, 2175, 3711, 3711, 3555,
    31383874217775, 55019636160209, 31383873809199, 234303542642613
  ]
def negativeCoefficients : Array ℕ := #[
    5537616353863440430708817920, 19331671319612877382755549184, 5537614541470835188745371648, 341521544041132741854494720, 363055535203018324028948480, 281878055362489122805514240,
    6227809693943659411370147840, 311959529858368762816757760, 281878055362489122805514240, 316209659692951443509084160, 316209659692951443509084160, 9359352579729007241928376320,
    303459270189203401432104960, 6227809693943659411370147840, 9359352579729007241928376320, 341521544041132741854494720, 311959529858368762816757760, 303459270189203401432104960,
    363055535203018324028948480, 126016749151853119076365762560, 438504971019467660903873249280, 126016707992555404611928719360, 38792011699794220957971775488, 38792011699794220957971775488,
    5537616353863440430708817920, 19331671319612877382755549184, 5537614541470835188745371648, 35890589732719110938676953088, 35890589732719110938676953088, 3249592603124123221610201088,
    400003330564990428180905984, 430141473458664503934713856, 333342405292802516344373248, 6942955429376472743241842688, 373737528187269461502328832, 333342405292802516344373248,
    378223776345995624455340032, 378223776345995624455340032, 11783126066527784126438703104, 364765031869817135596306432, 6942955429376472743241842688, 11783126066527784126438703104,
    400003330564990428180905984, 373737528187269461502328832, 364765031869817135596306432, 430141473458664503934713856, 156046835688075497934537359360, 545798826982992106958895448064,
    156046784553700925611660279808, 38792011699794220957971775488, 38792011699794220957971775488, 122354739743452784129568931840, 425267578270707158396985933824, 122354699809710629062210224128,
    820638189167524117857347567616, 820638189167524117857347567616, 84141237045178190559549849600, 35890589732719110938676953088, 35890589732719110938676953088, 68763700619680107457287290880,
    141340404232614006632113766400, 495572825818355039521711587328, 141340402392551285279585992704, 263802336834214756610067136512
  ]
def negativeScales : Array ℕ := #[
    32, 32, 32, 9, 12, 14,
    19, 14, 14, 12, 12, 15,
    13, 19, 15, 9, 14, 13,
    12, 30, 36, 34, 11, 11,
    32, 32, 32, 11, 11, 4,
    11, 15, 14, 18, 15, 14,
    14, 14, 20, 15, 18, 20,
    11, 15, 15, 15, 35, 36,
    35, 11, 11, 36, 38, 35,
    14, 14, 11, 11, 11, 11,
    44, 45, 44, 47
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32161323669193615, 32964953041373573, 32161323197017486, 9142107057302551, 12230320715661113, 14865201635645939,
    19330783421950795, 14011489349172888, 14865201635645939, 12031011907437707, 12031011907437707, 15918467304844059,
    13971633375310864, 19330783421950795, 15918467304844059, 9142107057302551, 14011489349172888, 13971633375310864,
    12230320715661113, 30669530249877639, 36468507949305510, 34669529778667861, 11969746265308618, 11969746265308618,
    32161323669193615, 32964953041373573, 32161323197017486, 11857592287698366, 11857592287698366, 4392317422778766,
    11370142479495401, 15474941707092834, 14107135324916144, 18487608471979704, 15272155903713022, 14107135324916144,
    14289370525595133, 14289370525595133, 20250708994178978, 15237097899518053, 18487608471979704, 20250708994178978,
    11370142479495401, 15272155903713022, 15237097899518053, 15474941707092834, 35977893870940564, 36784284046212582,
    35977893398189288, 11969746265308618, 11969746265308618, 36626984740959259, 38424285622095660, 35626984270097065,
    14372661044692482, 14372661044692482, 11086799685623454, 11857592287698366, 11857592287698366, 11795633845097634,
    44835088693252340, 45645011832830588, 44835088674470383, 47735372096334894
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
noncomputable def negativeCeiling : ℝ := 387303511 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5537616353863440430708817920, coefficient := (-5537616353863440430708817920) }, { argument := 19331671319612877382755549184, coefficient := (-19331671319612877382755549184) }, { argument := 5537614541470835188745371648, coefficient := (-5537614541470835188745371648) }, { argument := 341521544041132741854494720, coefficient := (-341521544041132741854494720) }, { argument := 363055535203018324028948480, coefficient := (-363055535203018324028948480) }, { argument := 281878055362489122805514240, coefficient := (-281878055362489122805514240) }, { argument := 6227809693943659411370147840, coefficient := (-6227809693943659411370147840) }, { argument := 311959529858368762816757760, coefficient := (-311959529858368762816757760) }, { argument := 281878055362489122805514240, coefficient := (-281878055362489122805514240) }, { argument := 316209659692951443509084160, coefficient := (-316209659692951443509084160) }, { argument := 316209659692951443509084160, coefficient := (-316209659692951443509084160) }, { argument := 9359352579729007241928376320, coefficient := (-9359352579729007241928376320) }, { argument := 303459270189203401432104960, coefficient := (-303459270189203401432104960) }, { argument := 6227809693943659411370147840, coefficient := (-6227809693943659411370147840) }, { argument := 9359352579729007241928376320, coefficient := (-9359352579729007241928376320) }, { argument := 341521544041132741854494720, coefficient := (-341521544041132741854494720) }, { argument := 311959529858368762816757760, coefficient := (-311959529858368762816757760) }, { argument := 303459270189203401432104960, coefficient := (-303459270189203401432104960) }, { argument := 363055535203018324028948480, coefficient := (-363055535203018324028948480) }, { argument := 126016749151853119076365762560, coefficient := (-126016749151853119076365762560) }, { argument := 438504971019467660903873249280, coefficient := (-438504971019467660903873249280) }, { argument := 126016707992555404611928719360, coefficient := (-126016707992555404611928719360) }, { argument := 38792011699794220957971775488, coefficient := (-38792011699794220957971775488) }, { argument := 38792011699794220957971775488, coefficient := (-38792011699794220957971775488) }, { argument := 5537616353863440430708817920, coefficient := (-5537616353863440430708817920) }, { argument := 19331671319612877382755549184, coefficient := (-19331671319612877382755549184) }, { argument := 5537614541470835188745371648, coefficient := (-5537614541470835188745371648) }, { argument := 35890589732719110938676953088, coefficient := (-35890589732719110938676953088) }, { argument := 35890589732719110938676953088, coefficient := (-35890589732719110938676953088) }, { argument := 3249592603124123221610201088, coefficient := (-3249592603124123221610201088) }, { argument := 400003330564990428180905984, coefficient := (-400003330564990428180905984) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 333342405292802516344373248, coefficient := (-333342405292802516344373248) }, { argument := 6942955429376472743241842688, coefficient := (-6942955429376472743241842688) }, { argument := 373737528187269461502328832, coefficient := (-373737528187269461502328832) }, { argument := 333342405292802516344373248, coefficient := (-333342405292802516344373248) }, { argument := 378223776345995624455340032, coefficient := (-378223776345995624455340032) }, { argument := 378223776345995624455340032, coefficient := (-378223776345995624455340032) }, { argument := 11783126066527784126438703104, coefficient := (-11783126066527784126438703104) }, { argument := 364765031869817135596306432, coefficient := (-364765031869817135596306432) }, { argument := 6942955429376472743241842688, coefficient := (-6942955429376472743241842688) }, { argument := 11783126066527784126438703104, coefficient := (-11783126066527784126438703104) }, { argument := 400003330564990428180905984, coefficient := (-400003330564990428180905984) }, { argument := 373737528187269461502328832, coefficient := (-373737528187269461502328832) }, { argument := 364765031869817135596306432, coefficient := (-364765031869817135596306432) }, { argument := 430141473458664503934713856, coefficient := (-430141473458664503934713856) }, { argument := 156046835688075497934537359360, coefficient := (-156046835688075497934537359360) }, { argument := 545798826982992106958895448064, coefficient := (-545798826982992106958895448064) }, { argument := 156046784553700925611660279808, coefficient := (-156046784553700925611660279808) }, { argument := 38792011699794220957971775488, coefficient := (-38792011699794220957971775488) }, { argument := 38792011699794220957971775488, coefficient := (-38792011699794220957971775488) }, { argument := 122354739743452784129568931840, coefficient := (-122354739743452784129568931840) }, { argument := 425267578270707158396985933824, coefficient := (-425267578270707158396985933824) }, { argument := 122354699809710629062210224128, coefficient := (-122354699809710629062210224128) }, { argument := 820638189167524117857347567616, coefficient := (-820638189167524117857347567616) }, { argument := 820638189167524117857347567616, coefficient := (-820638189167524117857347567616) }, { argument := 84141237045178190559549849600, coefficient := (-84141237045178190559549849600) }, { argument := 35890589732719110938676953088, coefficient := (-35890589732719110938676953088) }, { argument := 35890589732719110938676953088, coefficient := (-35890589732719110938676953088) }, { argument := 68763700619680107457287290880, coefficient := (-68763700619680107457287290880) }, { argument := 141340404232614006632113766400, coefficient := (-141340404232614006632113766400) }, { argument := 495572825818355039521711587328, coefficient := (-495572825818355039521711587328) }, { argument := 141340402392551285279585992704, coefficient := (-141340402392551285279585992704) }, { argument := 263802336834214756610067136512, coefficient := (-263802336834214756610067136512) }] }

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

end TermShard6


end Parent0

namespace Parent0

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 531688710866221409658923129281445888
def positiveArguments : Array ℕ := #[
    34601, 155, 1855, 2775, 805, 155,
    3215, 1615, 155, 1855, 155, 2205,
    1715, 245, 2303, 27195, 1911, 1715,
    27195, 245, 1911, 1911, 1911, 1911,
    1911, 2205, 2303, 1225, 5145, 22295,
    735, 735, 1715, 22295, 22295, 735,
    275135, 11025, 5145, 22295, 1715, 11025,
    1715, 22295, 22295, 735, 51, 969,
    1479, 15249, 459, 1479, 459, 459,
    39321
  ]
def positiveCoefficients : Array ℕ := #[
    5482747302312120690148428451151872, 2998136032644280353271316480, 71761836652324387810558607360, 53676306390889535356954214400, 62283858226545695080862187520, 2998136032644280353271316480,
    62187144160976524746885693440, 62477286357684035748815175680, 2998136032644280353271316480, 71761836652324387810558607360, 2998136032644280353271316480, 85301805832008234567267778560,
    66345848980450849107874938880, 75823827406229541837571358720, 89092997202319711659146346496, 1052055605261434892996302602240, 2365703415074361705332226392064, 66345848980450849107874938880,
    1052055605261434892996302602240, 75823827406229541837571358720, 73928231721073803291632074752, 73928231721073803291632074752, 73928231721073803291632074752, 2365703415074361705332226392064,
    73928231721073803291632074752, 85301805832008234567267778560, 89092997202319711659146346496, 23694946064446731824241049600, 398075093882705094647249633280, 862496036745861038402374205440,
    28433935277336078189089259520, 454942964437377251025428152320, 33172924490225424553937469440, 862496036745861038402374205440, 862496036745861038402374205440, 454942964437377251025428152320,
    10643769772149471935449079480320, 853018058320082345672677785600, 398075093882705094647249633280, 862496036745861038402374205440, 33172924490225424553937469440, 853018058320082345672677785600,
    33172924490225424553937469440, 862496036745861038402374205440, 862496036745861038402374205440, 28433935277336078189089259520, 31567471001777197009927667712, 37486371814610421449289105408,
    28608020595360584790246948864, 294958557172855684561511645184, 35513404876999346636168626176, 28608020595360584790246948864, 35513404876999346636168626176, 35513404876999346636168626176,
    1521157508898138680915889487872
  ]
def positiveScales : Array ℕ := #[
    15, 7, 10, 11, 9, 7,
    11, 10, 7, 10, 7, 11,
    10, 7, 11, 14, 10, 10,
    14, 7, 10, 10, 10, 10,
    10, 11, 11, 10, 12, 14,
    9, 9, 10, 14, 14, 9,
    18, 13, 12, 14, 10, 13,
    10, 14, 14, 9, 5, 9,
    10, 13, 8, 10, 8, 8,
    15
  ]
def negativeArguments : Array ℕ := #[
    234303486310475, 13621347, 4163, 4163, 3729, 165,
    5, 49, 245
  ]
def negativeCoefficients : Array ℕ := #[
    263802273409865830164227686400, 64324992524336993222642368512, 40262065496445610034414485504, 40262065496445610034414485504, 72129350101487235079669284864, 3191564163782621021224304640,
    396140812571321687967719751680, 7764359926397905084167307132928, 19410899815994762710418267832320
  ]
def negativeScales : Array ℕ := #[
    47, 23, 12, 12, 11, 7,
    2, 5, 7
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    15078526113197376, 7276124405274237, 10857203471385268, 11438272056124828, 9652844973000555, 7276124405274237,
    11650603022213964, 10657318449579693, 7276124405274237, 10857203471385268, 7276124405274237, 11106562940444882,
    10743992861047947, 7936637938489789, 11169298695792845, 14731053805343505, 10900112062706946, 10743992861047947,
    14731053805343505, 7936637938489789, 10900112062706946, 10900112062706946, 10900112062706946, 10900112062706946,
    10900112062706946, 11106562940444882, 11169298695792845, 10258566033889932, 12328955361781330, 14444432579201264,
    9521600439723692, 9521600439723692, 10743992861047947, 14444432579201264, 14444432579201264, 9521600439723692,
    18069780151403171, 13428491035332243, 12328955361781330, 14444432579201264, 10743992861047947, 13428491035332243,
    10743992861047947, 14444432579201264, 14444432579201264, 9521600439723692, 5672425341969176, 9920352855028171,
    10530406337099021, 13896427015916396, 8842350343321225, 10530406337099021, 8842350343321225, 8842350343321225,
    15263012391886529
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    47735371749476689, 23699366041210737, 12023407843140219, 12023407843140219, 11864573084055395, 7366322214245818,
    2321928094887363, 5614709844123661, 7936637947306280
  ]

abbrev PositiveTerm := Fin 55
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
noncomputable def positiveFloor : ℝ := 200075328973 / 200000000000
noncomputable def negativeCeiling : ℝ := 2582387407 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 263802273409865830164227686400, coefficient := (-263802273409865830164227686400) }, { argument := 64324992524336993222642368512, coefficient := (-64324992524336993222642368512) }, { argument := 40262065496445610034414485504, coefficient := (-40262065496445610034414485504) }, { argument := 40262065496445610034414485504, coefficient := (-40262065496445610034414485504) }, { argument := 72129350101487235079669284864, coefficient := (-72129350101487235079669284864) }, { argument := 3191564163782621021224304640, coefficient := (-3191564163782621021224304640) }, { argument := 5482747302312120690148428451151872, coefficient := 5482747302312120690148428451151872 }, { argument := 2998136032644280353271316480, coefficient := 2998136032644280353271316480 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 53676306390889535356954214400, coefficient := 53676306390889535356954214400 }, { argument := 62283858226545695080862187520, coefficient := 62283858226545695080862187520 }, { argument := 2998136032644280353271316480, coefficient := 2998136032644280353271316480 }, { argument := 62187144160976524746885693440, coefficient := 62187144160976524746885693440 }, { argument := 62477286357684035748815175680, coefficient := 62477286357684035748815175680 }, { argument := 2998136032644280353271316480, coefficient := 2998136032644280353271316480 }, { argument := 71761836652324387810558607360, coefficient := 71761836652324387810558607360 }, { argument := 2998136032644280353271316480, coefficient := 2998136032644280353271316480 }, { argument := 396140812571321687967719751680, coefficient := (-396140812571321687967719751680) }, { argument := 85301805832008234567267778560, coefficient := 85301805832008234567267778560 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 1052055605261434892996302602240, coefficient := 1052055605261434892996302602240 }, { argument := 2365703415074361705332226392064, coefficient := 2365703415074361705332226392064 }, { argument := 66345848980450849107874938880, coefficient := 66345848980450849107874938880 }, { argument := 1052055605261434892996302602240, coefficient := 1052055605261434892996302602240 }, { argument := 75823827406229541837571358720, coefficient := 75823827406229541837571358720 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 2365703415074361705332226392064, coefficient := 2365703415074361705332226392064 }, { argument := 73928231721073803291632074752, coefficient := 73928231721073803291632074752 }, { argument := 85301805832008234567267778560, coefficient := 85301805832008234567267778560 }, { argument := 89092997202319711659146346496, coefficient := 89092997202319711659146346496 }, { argument := 7764359926397905084167307132928, coefficient := (-7764359926397905084167307132928) }, { argument := 23694946064446731824241049600, coefficient := 23694946064446731824241049600 }, { argument := 398075093882705094647249633280, coefficient := 398075093882705094647249633280 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 28433935277336078189089259520, coefficient := 28433935277336078189089259520 }, { argument := 454942964437377251025428152320, coefficient := 454942964437377251025428152320 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 454942964437377251025428152320, coefficient := 454942964437377251025428152320 }, { argument := 10643769772149471935449079480320, coefficient := 10643769772149471935449079480320 }, { argument := 853018058320082345672677785600, coefficient := 853018058320082345672677785600 }, { argument := 398075093882705094647249633280, coefficient := 398075093882705094647249633280 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 853018058320082345672677785600, coefficient := 853018058320082345672677785600 }, { argument := 33172924490225424553937469440, coefficient := 33172924490225424553937469440 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 862496036745861038402374205440, coefficient := 862496036745861038402374205440 }, { argument := 28433935277336078189089259520, coefficient := 28433935277336078189089259520 }, { argument := 19410899815994762710418267832320, coefficient := (-19410899815994762710418267832320) }, { argument := 31567471001777197009927667712, coefficient := 31567471001777197009927667712 }, { argument := 37486371814610421449289105408, coefficient := 37486371814610421449289105408 }, { argument := 28608020595360584790246948864, coefficient := 28608020595360584790246948864 }, { argument := 294958557172855684561511645184, coefficient := 294958557172855684561511645184 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 28608020595360584790246948864, coefficient := 28608020595360584790246948864 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 35513404876999346636168626176, coefficient := 35513404876999346636168626176 }, { argument := 1521157508898138680915889487872, coefficient := 1521157508898138680915889487872 }] }

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

end TermShard7


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk13
