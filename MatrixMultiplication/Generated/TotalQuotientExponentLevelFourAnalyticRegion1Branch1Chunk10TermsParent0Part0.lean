import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 10, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16436271318877525563459549005873152)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3005335, 54061697, 12091, 243320975, 3769, 393,
    12013, 25117, 3769, 384779, 24647, 108123435,
    12013, 393, 24647, 393, 12013, 12559,
    3005335, 6442302106762343, 85437982665, 60913010167434381, 964228661505, 85437982665,
    121826015061941843, 85437982665, 85437982665, 3542014652769, 21969766971, 964228661505,
    3542014652769, 6442330513831103, 85437982665, 21969766971, 85437982665, 75006990567897735,
    4505322159, 116904567, 271586380054059429, 7257075813, 18754759876782837, 7257075813,
    7562826219, 4505322159, 224816475, 560912725, 10939308175, 21878608325,
    70114425, 73586928597, 264689993841, 36793476573, 3198557278577903, 560912725,
    3198558412159761, 560912725, 1909441261, 6868203433, 954720949, 85437982665,
    85437962295, 1485549, 6442304395985817, 85437962295
  ]
def negativeCoefficients : Array ℕ := #[
    28384586547590090396606136320, 2042393167358835600322667216896, 467747906718735403243915968512, 18384813070706605940809505177600, 291612250504162391005924950016, 15203451107473576501104869376,
    464730427872977288823849353216, 485833436980170255697520361472, 291612250504162391005924950016, 7442708287127958387428283121664, 476742314816668244303729917952, 2042393941826938790944482263040,
    464730427872977288823849353216, 15203451107473576501104869376, 476742314816668244303729917952, 15203451107473576501104869376, 464730427872977288823849353216, 485852779793284089764315660288,
    28384586547590090396606136320, 1813346835463940579612067627008, 98503287524705509575795671040, 68581952473018178108392413855744, 1111679959207390750926836858880, 98503287524705509575795671040,
    68581949504624214663360220758016, 98503287524705509575795671040, 98503287524705509575795671040, 4083664862809934125556557676544, 101317667168268524135104118784, 1111679959207390750926836858880,
    4083664862809934125556557676544, 1813354831342958218615684333568, 98503287524705509575795671040, 101317667168268524135104118784, 98503287524705509575795671040, 21112590923235409218599292764160,
    83108524836685572225519058944, 4313017256993662430865260544, 76444770000647746984046361575424, 133869420245918676219548663808, 21115982398125578547127583244288, 133869420245918676219548663808,
    139509519735833465552218619904, 83108524836685572225519058944, 4147131977878521568139673600, 1293376685720253181932339200, 50448654561915925142123315200, 50448636057525776202229350400,
    1293382853850302828563660800, 84839952437449854980217372672, 305166785953542779203869474816, 84839980740519871573703786496, 1800627670990828964840772468736, 1293376685720253181932339200,
    1800628309140683125185086226432, 1293376685720253181932339200, 4402871783181030398174953472, 15836998871840543431737737216, 4402873252003027267298000896, 98503287524705509575795671040,
    98503264039694460734322769920, 28061227225042074310243516416, 1813347479823064609249088765952, 98503264039694460734322769920
  ]
def negativeScales : Array ℕ := #[
    21, 25, 13, 27, 11, 8,
    13, 14, 11, 18, 14, 26,
    13, 8, 14, 8, 13, 13,
    21, 52, 36, 55, 39, 36,
    56, 36, 36, 41, 34, 39,
    41, 52, 36, 34, 36, 56,
    32, 26, 57, 32, 54, 32,
    32, 32, 27, 29, 33, 34,
    26, 36, 37, 35, 51, 29,
    51, 29, 30, 32, 29, 36,
    36, 20, 52, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21519094384188327, 25688103463135736, 13561645948818220, 27858285451415492, 11879966082700467, 8618385502267938,
    13552308859041758, 14616376537116341, 11879966082700467, 18553670538040564, 14589124433924909, 26688104010200375,
    13552308859041758, 8618385502267938, 14589124433924909, 8618385502267938, 13552308859041758, 13616433974960132,
    21519094384188327, 52516497739683340, 36314158531835892, 55757599918998995, 39810584358755788, 36314158531835892,
    56757599856555638, 36314158531835892, 36314158531835892, 41687707319011731, 34354800516333238, 39810584358755788,
    41687707319011731, 52516504101174340, 36314158531835892, 34354800516333238, 36314158531835892, 56057874577641744,
    32068983125524305, 26800756051126252, 57914188749535781, 32756741195867269, 54058106310027237, 32756741195867269,
    32816278323481299, 32068983125524305, 27744172522301705, 29063201071814004, 33348802450801467, 34348801921625872,
    26063207952028804, 36098730468918357, 37945512710632682, 35098730950209197, 51506342742053482, 29063201071814004,
    51506343253350449, 29063201071814004, 30830503395052475, 32677285625959142, 29830503876343326, 36314158531835892,
    36314158187870590, 20502564761768832, 52516498252334052, 36314158187870590
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
noncomputable def negativeCeiling : ℝ := 97910563451 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 28384586547590090396606136320, coefficient := (-28384586547590090396606136320) }, { argument := 2042393167358835600322667216896, coefficient := (-2042393167358835600322667216896) }, { argument := 467747906718735403243915968512, coefficient := (-467747906718735403243915968512) }, { argument := 18384813070706605940809505177600, coefficient := (-18384813070706605940809505177600) }, { argument := 291612250504162391005924950016, coefficient := (-291612250504162391005924950016) }, { argument := 15203451107473576501104869376, coefficient := (-15203451107473576501104869376) }, { argument := 464730427872977288823849353216, coefficient := (-464730427872977288823849353216) }, { argument := 485833436980170255697520361472, coefficient := (-485833436980170255697520361472) }, { argument := 291612250504162391005924950016, coefficient := (-291612250504162391005924950016) }, { argument := 7442708287127958387428283121664, coefficient := (-7442708287127958387428283121664) }, { argument := 476742314816668244303729917952, coefficient := (-476742314816668244303729917952) }, { argument := 2042393941826938790944482263040, coefficient := (-2042393941826938790944482263040) }, { argument := 464730427872977288823849353216, coefficient := (-464730427872977288823849353216) }, { argument := 15203451107473576501104869376, coefficient := (-15203451107473576501104869376) }, { argument := 476742314816668244303729917952, coefficient := (-476742314816668244303729917952) }, { argument := 15203451107473576501104869376, coefficient := (-15203451107473576501104869376) }, { argument := 464730427872977288823849353216, coefficient := (-464730427872977288823849353216) }, { argument := 485852779793284089764315660288, coefficient := (-485852779793284089764315660288) }, { argument := 28384586547590090396606136320, coefficient := (-28384586547590090396606136320) }, { argument := 1813346835463940579612067627008, coefficient := (-1813346835463940579612067627008) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 68581952473018178108392413855744, coefficient := (-68581952473018178108392413855744) }, { argument := 1111679959207390750926836858880, coefficient := (-1111679959207390750926836858880) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 68581949504624214663360220758016, coefficient := (-68581949504624214663360220758016) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 4083664862809934125556557676544, coefficient := (-4083664862809934125556557676544) }, { argument := 101317667168268524135104118784, coefficient := (-101317667168268524135104118784) }, { argument := 1111679959207390750926836858880, coefficient := (-1111679959207390750926836858880) }, { argument := 4083664862809934125556557676544, coefficient := (-4083664862809934125556557676544) }, { argument := 1813354831342958218615684333568, coefficient := (-1813354831342958218615684333568) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 101317667168268524135104118784, coefficient := (-101317667168268524135104118784) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 21112590923235409218599292764160, coefficient := (-21112590923235409218599292764160) }, { argument := 83108524836685572225519058944, coefficient := (-83108524836685572225519058944) }, { argument := 4313017256993662430865260544, coefficient := (-4313017256993662430865260544) }, { argument := 76444770000647746984046361575424, coefficient := (-76444770000647746984046361575424) }, { argument := 133869420245918676219548663808, coefficient := (-133869420245918676219548663808) }, { argument := 21115982398125578547127583244288, coefficient := (-21115982398125578547127583244288) }, { argument := 133869420245918676219548663808, coefficient := (-133869420245918676219548663808) }, { argument := 139509519735833465552218619904, coefficient := (-139509519735833465552218619904) }, { argument := 83108524836685572225519058944, coefficient := (-83108524836685572225519058944) }, { argument := 4147131977878521568139673600, coefficient := (-4147131977878521568139673600) }, { argument := 1293376685720253181932339200, coefficient := (-1293376685720253181932339200) }, { argument := 50448654561915925142123315200, coefficient := (-50448654561915925142123315200) }, { argument := 50448636057525776202229350400, coefficient := (-50448636057525776202229350400) }, { argument := 1293382853850302828563660800, coefficient := (-1293382853850302828563660800) }, { argument := 84839952437449854980217372672, coefficient := (-84839952437449854980217372672) }, { argument := 305166785953542779203869474816, coefficient := (-305166785953542779203869474816) }, { argument := 84839980740519871573703786496, coefficient := (-84839980740519871573703786496) }, { argument := 1800627670990828964840772468736, coefficient := (-1800627670990828964840772468736) }, { argument := 1293376685720253181932339200, coefficient := (-1293376685720253181932339200) }, { argument := 1800628309140683125185086226432, coefficient := (-1800628309140683125185086226432) }, { argument := 1293376685720253181932339200, coefficient := (-1293376685720253181932339200) }, { argument := 4402871783181030398174953472, coefficient := (-4402871783181030398174953472) }, { argument := 15836998871840543431737737216, coefficient := (-15836998871840543431737737216) }, { argument := 4402873252003027267298000896, coefficient := (-4402873252003027267298000896) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 28061227225042074310243516416, coefficient := (-28061227225042074310243516416) }, { argument := 1813347479823064609249088765952, coefficient := (-1813347479823064609249088765952) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }] }

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


end Parent0

namespace Parent0

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-49969259023285469005545966961426432)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    60913033470497651, 964228431615, 85437962295, 121826061668073901, 85437962295, 85437962295,
    3542013808287, 21969761733, 964228431615, 3542013808287, 6442332803074881, 85437962295,
    21969761733, 85437962295, 271590052743560513, 16205509827, 420502251, 983482938122485187,
    26103485889, 67908272249930047, 26103485889, 27203261007, 16205509827, 808658175,
    120933820787683877, 10939308175, 120933866960244187, 10939308175, 118532238279, 426356936187,
    59266138911, 964228661505, 964228431615, 110987761, 85437982665, 85437962295,
    11629, 9377382164373767, 2252661831, 58452303, 33953685077148947, 3628539117,
    4689444398615795, 3628539117, 3781414371, 2252661831, 112408275, 60466907715435465,
    21878608325, 60466930801718327, 21878608325, 504179469, 85437982665, 85437962295,
    3625, 189, 560912725, 10939308175, 21878608325, 70114425,
    118532238279, 426356936187, 59266138911, 85437982665
  ]
def negativeCoefficients : Array ℕ := #[
    68581978709934942949165418676224, 1111679694162266056858785546240, 98503264039694460734322769920, 68581975741544085861976204378112, 98503264039694460734322769920, 98503264039694460734322769920,
    4083663889188476072157209690112, 101317643012257159612446277632, 1111679694162266056858785546240, 4083663889188476072157209690112, 1813355475707797316179838631936, 98503264039694460734322769920,
    101317643012257159612446277632, 98503264039694460734322769920, 76445803770839530073750427926528, 298938892362654151056851730432, 15513794813231552749457375232, 276825837103354053945553345052672,
    481524323626071656492773146624, 76457917400039788420200637923328, 481524323626071656492773146624, 501811593766451379318986637312, 298938892362654151056851730432, 14917110397338031489862860800,
    68079688779487931439708450586624, 50448654561915925142123315200, 68079714772328607296927609913344, 50448654561915925142123315200, 136658366501041981974122594304, 491556080368281482669705920512,
    136658412091017038642672566272, 1111679959207390750926836858880, 1111679694162266056858785546240, 2096499530220587108529942298624, 98503287524705509575795671040, 98503264039694460734322769920,
    449875147401552725525059862528, 21115987410592216166078366089216, 83108552562141915010975137792, 4313018695839700180210286592, 76456901730651584219493072633856, 133869464905486078670373126144,
    21119380046180754070218022584320, 133869464905486078670373126144, 139509566276968763521417347072, 83108552562141915010975137792, 4147133361384327096356044800, 68079685763870332439377383260160,
    50448636057525776202229350400, 68079711756714056107644365570048, 50448636057525776202229350400, 19047361806052922560477126459392, 98503287524705509575795671040, 98503264039694460734322769920,
    280470790150593968531832832000, 14623166714058554497245904896, 1293376685720253181932339200, 50448654561915925142123315200, 50448636057525776202229350400, 1293382853850302828563660800,
    136658366501041981974122594304, 491556080368281482669705920512, 136658412091017038642672566272, 98503287524705509575795671040
  ]
def negativeScales : Array ℕ := #[
    55, 39, 36, 56, 36, 36,
    41, 34, 39, 41, 52, 36,
    34, 36, 57, 33, 28, 59,
    34, 55, 34, 34, 33, 29,
    56, 33, 56, 33, 36, 38,
    35, 39, 39, 26, 36, 36,
    13, 53, 31, 25, 54, 31,
    52, 31, 31, 31, 26, 55,
    34, 55, 34, 28, 36, 36,
    11, 7, 29, 33, 34, 26,
    36, 38, 35, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    55757600470920621, 39810584014790481, 36314158187870590, 56757600408477352, 36314158187870590, 36314158187870590,
    41687706975046429, 34354800172367937, 39810584014790481, 41687706975046429, 52516504613827339, 36314158187870590,
    34354800172367937, 36314158187870590, 57914208259113645, 33915765363355779, 28647538282543074, 59770677637674025,
    34603523427665984, 55914436850993709, 34603523427665984, 34663060554666718, 33915765363355779, 29590954754161090,
    56746995383599958, 33348802450801467, 56746995934421150, 33348802450801467, 36786488539490164, 38633270771067643,
    35786489020781008, 39810584358755788, 39810584014790481, 26725825353660354, 36314158531835892, 36314158187870590,
    13505439421582818, 53058106652491053, 31068983606815145, 25800756532417098, 54914417686058046, 31756741677158111,
    52058338426894563, 31756741677158111, 31816278804772148, 31068983606815145, 26744173003592547, 55746995319695191,
    34348801921625872, 55746995870516472, 34348801921625872, 28909362134786724, 36314158531835892, 36314158187870590,
    11823765280830443, 7562242424222992, 29063201071814004, 33348802450801467, 34348801921625872, 26063207952028804,
    36786488539490164, 38633270771067643, 35786489020781008, 36314158531835892
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
noncomputable def negativeCeiling : ℝ := 84455771313 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 68581978709934942949165418676224, coefficient := (-68581978709934942949165418676224) }, { argument := 1111679694162266056858785546240, coefficient := (-1111679694162266056858785546240) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 68581975741544085861976204378112, coefficient := (-68581975741544085861976204378112) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 4083663889188476072157209690112, coefficient := (-4083663889188476072157209690112) }, { argument := 101317643012257159612446277632, coefficient := (-101317643012257159612446277632) }, { argument := 1111679694162266056858785546240, coefficient := (-1111679694162266056858785546240) }, { argument := 4083663889188476072157209690112, coefficient := (-4083663889188476072157209690112) }, { argument := 1813355475707797316179838631936, coefficient := (-1813355475707797316179838631936) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 101317643012257159612446277632, coefficient := (-101317643012257159612446277632) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 76445803770839530073750427926528, coefficient := (-76445803770839530073750427926528) }, { argument := 298938892362654151056851730432, coefficient := (-298938892362654151056851730432) }, { argument := 15513794813231552749457375232, coefficient := (-15513794813231552749457375232) }, { argument := 276825837103354053945553345052672, coefficient := (-276825837103354053945553345052672) }, { argument := 481524323626071656492773146624, coefficient := (-481524323626071656492773146624) }, { argument := 76457917400039788420200637923328, coefficient := (-76457917400039788420200637923328) }, { argument := 481524323626071656492773146624, coefficient := (-481524323626071656492773146624) }, { argument := 501811593766451379318986637312, coefficient := (-501811593766451379318986637312) }, { argument := 298938892362654151056851730432, coefficient := (-298938892362654151056851730432) }, { argument := 14917110397338031489862860800, coefficient := (-14917110397338031489862860800) }, { argument := 68079688779487931439708450586624, coefficient := (-68079688779487931439708450586624) }, { argument := 50448654561915925142123315200, coefficient := (-50448654561915925142123315200) }, { argument := 68079714772328607296927609913344, coefficient := (-68079714772328607296927609913344) }, { argument := 50448654561915925142123315200, coefficient := (-50448654561915925142123315200) }, { argument := 136658366501041981974122594304, coefficient := (-136658366501041981974122594304) }, { argument := 491556080368281482669705920512, coefficient := (-491556080368281482669705920512) }, { argument := 136658412091017038642672566272, coefficient := (-136658412091017038642672566272) }, { argument := 1111679959207390750926836858880, coefficient := (-1111679959207390750926836858880) }, { argument := 1111679694162266056858785546240, coefficient := (-1111679694162266056858785546240) }, { argument := 2096499530220587108529942298624, coefficient := (-2096499530220587108529942298624) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 449875147401552725525059862528, coefficient := (-449875147401552725525059862528) }, { argument := 21115987410592216166078366089216, coefficient := (-21115987410592216166078366089216) }, { argument := 83108552562141915010975137792, coefficient := (-83108552562141915010975137792) }, { argument := 4313018695839700180210286592, coefficient := (-4313018695839700180210286592) }, { argument := 76456901730651584219493072633856, coefficient := (-76456901730651584219493072633856) }, { argument := 133869464905486078670373126144, coefficient := (-133869464905486078670373126144) }, { argument := 21119380046180754070218022584320, coefficient := (-21119380046180754070218022584320) }, { argument := 133869464905486078670373126144, coefficient := (-133869464905486078670373126144) }, { argument := 139509566276968763521417347072, coefficient := (-139509566276968763521417347072) }, { argument := 83108552562141915010975137792, coefficient := (-83108552562141915010975137792) }, { argument := 4147133361384327096356044800, coefficient := (-4147133361384327096356044800) }, { argument := 68079685763870332439377383260160, coefficient := (-68079685763870332439377383260160) }, { argument := 50448636057525776202229350400, coefficient := (-50448636057525776202229350400) }, { argument := 68079711756714056107644365570048, coefficient := (-68079711756714056107644365570048) }, { argument := 50448636057525776202229350400, coefficient := (-50448636057525776202229350400) }, { argument := 19047361806052922560477126459392, coefficient := (-19047361806052922560477126459392) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }, { argument := 98503264039694460734322769920, coefficient := (-98503264039694460734322769920) }, { argument := 280470790150593968531832832000, coefficient := (-280470790150593968531832832000) }, { argument := 14623166714058554497245904896, coefficient := (-14623166714058554497245904896) }, { argument := 1293376685720253181932339200, coefficient := (-1293376685720253181932339200) }, { argument := 50448654561915925142123315200, coefficient := (-50448654561915925142123315200) }, { argument := 50448636057525776202229350400, coefficient := (-50448636057525776202229350400) }, { argument := 1293382853850302828563660800, coefficient := (-1293382853850302828563660800) }, { argument := 136658366501041981974122594304, coefficient := (-136658366501041981974122594304) }, { argument := 491556080368281482669705920512, coefficient := (-491556080368281482669705920512) }, { argument := 136658412091017038642672566272, coefficient := (-136658412091017038642672566272) }, { argument := 98503287524705509575795671040, coefficient := (-98503287524705509575795671040) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
