import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 18, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-565196964870634263466272163364864)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    17016247221, 34032481959, 109063971, 20127401, 2352502425, 644076615,
    25347881, 4445780183, 1111445179, 6336837, 34169949, 16154674371,
    613218558249, 64618741803, 34169949, 1699093761, 33136902483, 66273780657,
    212387733, 34169949, 16154674371, 613218558249, 64618741803, 34169949,
    52671906591, 1027243976973, 2054487200367, 6584019723, 205818907, 24056234475,
    6586202805, 1699093761, 33136902483, 66273780657, 212387733, 410988543,
    48036581775, 13151628945, 2597499, 691463007, 17115429, 23307579189,
    5416275, 649953, 17115429, 34014207, 5416275, 524945373,
    33580905, 2765853711, 17115429, 649953, 33580905, 649953,
    17115429, 17115429, 2597499, 143756415, 3412143, 2689439013,
    35702667, 1581237, 5378876055, 1581237
  ]
def negativeCoefficients : Array ℕ := #[
    78473589395189594211729014784, 78473560611351310197187411968, 2011875160699480399870427136, 742570030231851405810860032, 2712250635422256182643916800, 742569780047884906125066240,
    116896468404461235731431424, 20502542310942653968057106432, 20502544768971301789854859264, 116894010375813413933678592, 1260648608429415239063175168, 149000571857975914194448416768,
    1413985725658557028392971010048, 149000674050632239536150675456, 1260648608429415239063175168, 1958921735400226454803316736, 76408494937421446995630882816, 76408466911052591507787743232,
    1958931077523178284084363264, 1260648608429415239063175168, 149000571857975914194448416768, 1413985725658557028392971010048, 149000674050632239536150675456, 1260648608429415239063175168,
    60726573797407020098902818816, 2368663343060064856864557367296, 2368662474242630336741420040192, 60726863403218526806615261184, 15186754811838509396260814848, 55469900092184207090201395200,
    15186749695172871951073935360, 1958921735400226454803316736, 76408494937421446995630882816, 76408466911052591507787743232, 1958931077523178284084363264, 15162800939895546447686270976,
    55382408136202843987535462400, 15162795831300359534747320320, 95830798569432973226016768, 6377620563283318102510534656, 1262895753898986389221933056, 53743618534650228409450364928,
    799301110062649613431603200, 47958066603758976805896192, 1262895753898986389221933056, 1254902742798359893087617024, 799301110062649613431603200, 19367065896818000133447745536,
    1238916720597106900818984960, 6377624444017102609157455872, 1262895753898986389221933056, 47958066603758976805896192, 1238916720597106900818984960, 47958066603758976805896192,
    1262895753898986389221933056, 1262895753898986389221933056, 95830798569432973226016768, 2651837796458980891573616640, 125885857327799061159346176, 99222786349322031493615190016,
    1317195921795751152130719744, 116674697035521081074515968, 99222749990789462212088954880, 116674697035521081074515968
  ]
def negativeScales : Array ℕ := #[
    33, 34, 26, 24, 31, 29,
    24, 32, 30, 22, 25, 33,
    39, 35, 25, 30, 34, 35,
    27, 25, 33, 39, 35, 25,
    35, 39, 40, 32, 27, 34,
    32, 30, 34, 35, 27, 28,
    35, 33, 21, 29, 24, 34,
    22, 19, 24, 25, 22, 28,
    25, 31, 24, 19, 25, 19,
    24, 24, 21, 27, 21, 31,
    25, 20, 32, 20
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33986193866635986, 34986193337460228, 26700599348971106, 24262657556963254, 31131549064095726, 29262657070895659,
    24595361811896065, 32049789471551406, 30049789644514615, 22595331475453283, 25026224758700931, 33911232624769567,
    39157610402676557, 35911233614247661, 25026224758700931, 30662118320897169, 34947719709885504, 35947719180709819,
    27662125201111974, 25026224758700931, 33911232624769567, 39157610402676557, 35911233614247661, 25026224758700931,
    35616314631263956, 39901916014762661, 40901915485587023, 32616321511478758, 27616800276724727, 34485691783848424,
    32616799790657132, 30662118320897169, 34947719709885504, 35947719180709819, 27662125201111974, 28614522936013129,
    35483414443137346, 33614522449945534, 21308691763036792, 29365076828919719, 24028794118313064, 34440080117502173,
    22368869559910687, 19309975870857117, 24028794118313064, 25019634119027588, 22368869559910687, 28967592073574580,
    25001137775410198, 31365077706788452, 24028794118313064, 19309975870857117, 25001137775410198, 19309975870857117,
    24028794118313064, 24028794118313064, 21308691763036792, 27099051095553747, 21702246679441138, 31324658128044751,
    25089528512246290, 20592622188194934, 32324657599393157, 20592622188194934
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
noncomputable def negativeCeiling : ℝ := 135564963 / 31250000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 78473589395189594211729014784, coefficient := (-78473589395189594211729014784) }, { argument := 78473560611351310197187411968, coefficient := (-78473560611351310197187411968) }, { argument := 2011875160699480399870427136, coefficient := (-2011875160699480399870427136) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 116896468404461235731431424, coefficient := (-116896468404461235731431424) }, { argument := 20502542310942653968057106432, coefficient := (-20502542310942653968057106432) }, { argument := 20502544768971301789854859264, coefficient := (-20502544768971301789854859264) }, { argument := 116894010375813413933678592, coefficient := (-116894010375813413933678592) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 149000571857975914194448416768, coefficient := (-149000571857975914194448416768) }, { argument := 1413985725658557028392971010048, coefficient := (-1413985725658557028392971010048) }, { argument := 149000674050632239536150675456, coefficient := (-149000674050632239536150675456) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 1958921735400226454803316736, coefficient := (-1958921735400226454803316736) }, { argument := 76408494937421446995630882816, coefficient := (-76408494937421446995630882816) }, { argument := 76408466911052591507787743232, coefficient := (-76408466911052591507787743232) }, { argument := 1958931077523178284084363264, coefficient := (-1958931077523178284084363264) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 149000571857975914194448416768, coefficient := (-149000571857975914194448416768) }, { argument := 1413985725658557028392971010048, coefficient := (-1413985725658557028392971010048) }, { argument := 149000674050632239536150675456, coefficient := (-149000674050632239536150675456) }, { argument := 1260648608429415239063175168, coefficient := (-1260648608429415239063175168) }, { argument := 60726573797407020098902818816, coefficient := (-60726573797407020098902818816) }, { argument := 2368663343060064856864557367296, coefficient := (-2368663343060064856864557367296) }, { argument := 2368662474242630336741420040192, coefficient := (-2368662474242630336741420040192) }, { argument := 60726863403218526806615261184, coefficient := (-60726863403218526806615261184) }, { argument := 15186754811838509396260814848, coefficient := (-15186754811838509396260814848) }, { argument := 55469900092184207090201395200, coefficient := (-55469900092184207090201395200) }, { argument := 15186749695172871951073935360, coefficient := (-15186749695172871951073935360) }, { argument := 1958921735400226454803316736, coefficient := (-1958921735400226454803316736) }, { argument := 76408494937421446995630882816, coefficient := (-76408494937421446995630882816) }, { argument := 76408466911052591507787743232, coefficient := (-76408466911052591507787743232) }, { argument := 1958931077523178284084363264, coefficient := (-1958931077523178284084363264) }, { argument := 15162800939895546447686270976, coefficient := (-15162800939895546447686270976) }, { argument := 55382408136202843987535462400, coefficient := (-55382408136202843987535462400) }, { argument := 15162795831300359534747320320, coefficient := (-15162795831300359534747320320) }, { argument := 95830798569432973226016768, coefficient := (-95830798569432973226016768) }, { argument := 6377620563283318102510534656, coefficient := (-6377620563283318102510534656) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 53743618534650228409450364928, coefficient := (-53743618534650228409450364928) }, { argument := 799301110062649613431603200, coefficient := (-799301110062649613431603200) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 1254902742798359893087617024, coefficient := (-1254902742798359893087617024) }, { argument := 799301110062649613431603200, coefficient := (-799301110062649613431603200) }, { argument := 19367065896818000133447745536, coefficient := (-19367065896818000133447745536) }, { argument := 1238916720597106900818984960, coefficient := (-1238916720597106900818984960) }, { argument := 6377624444017102609157455872, coefficient := (-6377624444017102609157455872) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1238916720597106900818984960, coefficient := (-1238916720597106900818984960) }, { argument := 47958066603758976805896192, coefficient := (-47958066603758976805896192) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 1262895753898986389221933056, coefficient := (-1262895753898986389221933056) }, { argument := 95830798569432973226016768, coefficient := (-95830798569432973226016768) }, { argument := 2651837796458980891573616640, coefficient := (-2651837796458980891573616640) }, { argument := 125885857327799061159346176, coefficient := (-125885857327799061159346176) }, { argument := 99222786349322031493615190016, coefficient := (-99222786349322031493615190016) }, { argument := 1317195921795751152130719744, coefficient := (-1317195921795751152130719744) }, { argument := 116674697035521081074515968, coefficient := (-116674697035521081074515968) }, { argument := 99222749990789462212088954880, coefficient := (-99222749990789462212088954880) }, { argument := 116674697035521081074515968, coefficient := (-116674697035521081074515968) }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 19019659675825647943890943963299840
def positiveArguments : Array ℕ := #[
    1685, 217, 5257, 3983, 2219, 217,
    2219, 4431, 217, 5257, 217, 1317,
    3951, 8341, 21511, 17999, 503533, 15365,
    17999, 16243, 8341, 8341, 16243, 503533,
    16243, 1317, 21511, 3369, 50535, 88717,
    3369, 28075, 3369, 88717, 176311, 28075,
    2721029, 174065, 50535, 88717
  ]
def positiveCoefficients : Array ℕ := #[
    133499453836535408845121556316160, 8394780891403984989159686144, 203370337078851378285771751424, 154084849264802176091350368256, 171686809198391176875072290816, 8394780891403984989159686144,
    171686809198391176875072290816, 171416009814797499939938107392, 8394780891403984989159686144, 203370337078851378285771751424, 8394780891403984989159686144, 407591757934711455510536650752,
    305693818451033591632902488064, 322676808364979902279174848512, 416083252891684610833672830976, 5570420691774389891977334226944, 9739744715648209155637198716928, 297202323494060436309766307840,
    5570420691774389891977334226944, 314185313408006746956038668288, 322676808364979902279174848512, 322676808364979902279174848512, 314185313408006746956038668288, 9739744715648209155637198716928,
    314185313408006746956038668288, 407591757934711455510536650752, 416083252891684610833672830976, 130331874761013942066723422208, 1954978121415209131000851333120, 3432072702040033807757050118144,
    130331874761013942066723422208, 2172197912683565701112057036800, 130331874761013942066723422208, 3432072702040033807757050118144, 3410350722913198150745929547776, 2172197912683565701112057036800,
    52632355424322796937945142001664, 3366906764659526836723688407040, 1954978121415209131000851333120, 3432072702040033807757050118144
  ]
def positiveScales : Array ℕ := #[
    10, 7, 12, 11, 11, 7,
    11, 12, 7, 12, 7, 10,
    11, 13, 14, 14, 18, 13,
    14, 13, 13, 13, 13, 18,
    13, 10, 14, 11, 15, 16,
    11, 14, 11, 16, 17, 14,
    21, 17, 15, 16
  ]
def negativeArguments : Array ℕ := #[
    3079251, 58172877, 3079251, 35702667, 58172877, 8984817,
    3079251, 3079251, 3412143, 20127401, 2352502425, 644076615,
    2250151197, 43884005991, 87767979789, 281270241, 487602521, 56991268425,
    15603275415, 20127401, 2352502425, 644076615, 7, 439
  ]
def negativeCoefficients : Array ℕ := #[
    113604310271428421046239232, 4292400696201538719530876928, 113604310271428421046239232, 1317195921795751152130719744, 4292400696201538719530876928, 2651849915969837318749028352,
    113604310271428421046239232, 113604310271428421046239232, 125885857327799061159346176, 742570030231851405810860032, 2712250635422256182643916800, 742569780047884906125066240,
    2594247703638137737442230272, 101189628430639213588808466432, 101189591314637215780583768064, 2594260075638803673517129728, 17989357829165174379482447872, 65706458942003690102115532800,
    17989351768256824661287895040, 742570030231851405810860032, 2712250635422256182643916800, 742569780047884906125066240, 1109194275199700726309615304704, 34781163343762044203565794197504
  ]
def negativeScales : Array ℕ := #[
    21, 25, 21, 25, 25, 23,
    21, 21, 21, 24, 31, 29,
    31, 35, 36, 28, 28, 35,
    33, 24, 31, 29, 2, 8
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    10718532876062314, 7761551232426566, 12360024019571875, 11959639763607828, 11115693952197011, 7761551232426566,
    11115693952197011, 12113416611485945, 7761551232426566, 12360024019571875, 7761551232426566, 10363039630256513,
    11948002130355516, 13026004642978943, 14392786973650565, 14135629134153441, 18941726804991849, 13907360146172515,
    14135629134153441, 13987530493969150, 13026004642978943, 13026004642978943, 13987530493969150, 18941726804991849,
    13987530493969150, 10363039630256513, 14392786973650565, 11718104713114918, 15624995308729583, 16436922960577701,
    11718104713114918, 14776998402150455, 11718104713114918, 16436922960577701, 17427762961292226, 14776998402150455,
    21375720901851947, 17409266617674837, 15624995308729583, 16436922960577701
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    21554148040377201, 25793843320691708, 21554148040377201, 25089528512246290, 25793843320691708, 23099057688988036,
    21554148040377201, 21554148040377201, 21702246679441138, 24262657556963254, 31131549064095726, 29262657070895659,
    31067374799354514, 35352976178341977, 36352975649166382, 28067381679569314, 28861130346229564, 35730021851367526,
    33861129860161949, 24262657556963254, 31131549064095726, 29262657070895659, 2807354922807594, 8778077129945769
  ]

abbrev PositiveTerm := Fin 40
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 42931618523 / 1000000000000
noncomputable def negativeCeiling : ℝ := 1925253467 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 113604310271428421046239232, coefficient := (-113604310271428421046239232) }, { argument := 4292400696201538719530876928, coefficient := (-4292400696201538719530876928) }, { argument := 113604310271428421046239232, coefficient := (-113604310271428421046239232) }, { argument := 1317195921795751152130719744, coefficient := (-1317195921795751152130719744) }, { argument := 4292400696201538719530876928, coefficient := (-4292400696201538719530876928) }, { argument := 2651849915969837318749028352, coefficient := (-2651849915969837318749028352) }, { argument := 113604310271428421046239232, coefficient := (-113604310271428421046239232) }, { argument := 113604310271428421046239232, coefficient := (-113604310271428421046239232) }, { argument := 125885857327799061159346176, coefficient := (-125885857327799061159346176) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 2594247703638137737442230272, coefficient := (-2594247703638137737442230272) }, { argument := 101189628430639213588808466432, coefficient := (-101189628430639213588808466432) }, { argument := 101189591314637215780583768064, coefficient := (-101189591314637215780583768064) }, { argument := 2594260075638803673517129728, coefficient := (-2594260075638803673517129728) }, { argument := 17989357829165174379482447872, coefficient := (-17989357829165174379482447872) }, { argument := 65706458942003690102115532800, coefficient := (-65706458942003690102115532800) }, { argument := 17989351768256824661287895040, coefficient := (-17989351768256824661287895040) }, { argument := 742570030231851405810860032, coefficient := (-742570030231851405810860032) }, { argument := 2712250635422256182643916800, coefficient := (-2712250635422256182643916800) }, { argument := 742569780047884906125066240, coefficient := (-742569780047884906125066240) }, { argument := 133499453836535408845121556316160, coefficient := 133499453836535408845121556316160 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 154084849264802176091350368256, coefficient := 154084849264802176091350368256 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 171686809198391176875072290816, coefficient := 171686809198391176875072290816 }, { argument := 171416009814797499939938107392, coefficient := 171416009814797499939938107392 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 203370337078851378285771751424, coefficient := 203370337078851378285771751424 }, { argument := 8394780891403984989159686144, coefficient := 8394780891403984989159686144 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 407591757934711455510536650752, coefficient := 407591757934711455510536650752 }, { argument := 305693818451033591632902488064, coefficient := 305693818451033591632902488064 }, { argument := 322676808364979902279174848512, coefficient := 322676808364979902279174848512 }, { argument := 416083252891684610833672830976, coefficient := 416083252891684610833672830976 }, { argument := 5570420691774389891977334226944, coefficient := 5570420691774389891977334226944 }, { argument := 9739744715648209155637198716928, coefficient := 9739744715648209155637198716928 }, { argument := 297202323494060436309766307840, coefficient := 297202323494060436309766307840 }, { argument := 5570420691774389891977334226944, coefficient := 5570420691774389891977334226944 }, { argument := 314185313408006746956038668288, coefficient := 314185313408006746956038668288 }, { argument := 322676808364979902279174848512, coefficient := 322676808364979902279174848512 }, { argument := 322676808364979902279174848512, coefficient := 322676808364979902279174848512 }, { argument := 314185313408006746956038668288, coefficient := 314185313408006746956038668288 }, { argument := 9739744715648209155637198716928, coefficient := 9739744715648209155637198716928 }, { argument := 314185313408006746956038668288, coefficient := 314185313408006746956038668288 }, { argument := 407591757934711455510536650752, coefficient := 407591757934711455510536650752 }, { argument := 416083252891684610833672830976, coefficient := 416083252891684610833672830976 }, { argument := 34781163343762044203565794197504, coefficient := (-34781163343762044203565794197504) }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 1954978121415209131000851333120, coefficient := 1954978121415209131000851333120 }, { argument := 3432072702040033807757050118144, coefficient := 3432072702040033807757050118144 }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 2172197912683565701112057036800, coefficient := 2172197912683565701112057036800 }, { argument := 130331874761013942066723422208, coefficient := 130331874761013942066723422208 }, { argument := 3432072702040033807757050118144, coefficient := 3432072702040033807757050118144 }, { argument := 3410350722913198150745929547776, coefficient := 3410350722913198150745929547776 }, { argument := 2172197912683565701112057036800, coefficient := 2172197912683565701112057036800 }, { argument := 52632355424322796937945142001664, coefficient := 52632355424322796937945142001664 }, { argument := 3366906764659526836723688407040, coefficient := 3366906764659526836723688407040 }, { argument := 1954978121415209131000851333120, coefficient := 1954978121415209131000851333120 }, { argument := 3432072702040033807757050118144, coefficient := 3432072702040033807757050118144 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
