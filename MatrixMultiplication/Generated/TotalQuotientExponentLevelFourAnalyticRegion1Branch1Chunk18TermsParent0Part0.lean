import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 18, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent0

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4647506604067306657932633243123712)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    93, 2253, 1707, 951, 93, 951,
    1899, 93, 2253, 93, 181446735661623, 4142503930262985,
    479306297, 1236123795, 1034309179, 28937849201, 1034801459895653, 1034309179,
    933509231, 479337529, 479306297, 933446767, 28937849201, 933446767,
    45361572766363, 1236123795, 13762680791293, 4544749261673715, 19830414969, 162796050298200025,
    6275447775, 753053733, 19830414969, 39409812027, 6275447775, 608216398353,
    38907776205, 18179017088838843, 19830414969, 753053733, 38907776205, 753053733,
    19830414969, 19830414969, 13762680791293, 3149, 2345, 2479,
    201, 43081, 77921, 2345, 43081, 1273,
    1273, 2479, 2479, 77921, 2479, 3149,
    201, 4803645, 196806225, 4052392575
  ]
def negativeCoefficients : Array ℕ := #[
    1798881619586568211962789888, 43579357945468152489808232448, 33018181985314752019575078912, 36790030542512395044658348032, 1798881619586568211962789888, 36790030542512395044658348032,
    36732002103170892844272451584, 1798881619586568211962789888, 43579357945468152489808232448, 1798881619586568211962789888, 102145431389159778848788709376, 2332022394589149299256663736320,
    70733124749411361908762607616, 91209837159150442685273210880, 1221096749958505076249797328896, 2135236393017789733348535435264, 2330165734594254055703465426944, 1221096749958505076249797328896,
    68880823498809643385627869184, 70737733779098642682491174912, 70733124749411361908762607616, 68876214469122362611899301888, 2135236393017789733348535435264, 68876214469122362611899301888,
    102145181103766023105123713024, 91209837159150442685273210880, 61981604083286237830161891328, 5116932770341519923039342428160, 731613179617203863448409079808, 45823014466272634800792036966400,
    463046316213420166739499417600, 27782778972805210004369965056, 731613179617203863448409079808, 726982716455069661781014085632, 463046316213420166739499417600, 11219612241851170640098070888448,
    717721790130801258446224097280, 5116938411703530769578624811008, 731613179617203863448409079808, 27782778972805210004369965056, 717721790130801258446224097280, 27782778972805210004369965056,
    731613179617203863448409079808, 731613179617203863448409079808, 61981604083286237830161891328, 237931712872904204446859264, 177183190437269088417873920, 187307944176541607756038144,
    242994089742540464115941376, 3255108327176114967219798016, 5887544299386969995142496256, 177183190437269088417873920, 3255108327176114967219798016, 192370321046177867425120256,
    192370321046177867425120256, 187307944176541607756038144, 187307944176541607756038144, 5887544299386969995142496256, 187307944176541607756038144, 237931712872904204446859264,
    242994089742540464115941376, 177223219871909038144880640, 29043472517503188799900876800, 299013794868903358701030604800
  ]
def negativeScales : Array ℕ := #[
    6, 11, 10, 9, 6, 9,
    10, 6, 11, 6, 47, 51,
    28, 30, 29, 34, 49, 29,
    29, 28, 28, 29, 34, 29,
    45, 30, 43, 52, 34, 57,
    32, 29, 34, 35, 32, 39,
    35, 54, 34, 29, 35, 29,
    34, 34, 43, 11, 11, 11,
    7, 15, 16, 11, 15, 10,
    10, 11, 11, 16, 11, 11,
    7, 22, 27, 31
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    6539158811108986, 11137631598235429, 10737247343197484, 9893301534732022, 6539158811108986, 9893301534732022,
    10891024193864606, 6539158811108986, 11137631598235429, 6539158811108986, 47366539430502648, 51879424492542489,
    28836372654260412, 30203176087106522, 29946020368857950, 34752238646986265, 49878275420741326, 29946020368857950,
    29798089048322821, 28836466658418115, 28836372654260412, 29797992509888805, 34752238646986265, 29797992509888805,
    45366535895484646, 30203176087106522, 43645826749205629, 52013122125008486, 34206995816428004, 57175843310942863,
    32547071258026842, 29488177568972239, 34206995816428004, 35197835817142528, 32547071258026842, 39145793757702248,
    35179339473525139, 54013123715562998, 34206995816428004, 29488177568972239, 35179339473525139, 29488177568972239,
    34206995816428004, 34206995816428004, 43645826749205629, 11620678042145331, 11195372207402739, 11275542556086723,
    7651051691200812, 15394764117785726, 16249724571930991, 11195372207402739, 15394764117785726, 10314016703901359,
    10314016703901359, 11275542556086723, 11275542556086723, 16249724571930991, 11275542556086723, 11620678042145331,
    7651051691200812, 22195698105949777, 27552200613083350, 31916126801604000
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
noncomputable def negativeCeiling : ℝ := 3265129521 / 62500000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 43579357945468152489808232448, coefficient := (-43579357945468152489808232448) }, { argument := 33018181985314752019575078912, coefficient := (-33018181985314752019575078912) }, { argument := 36790030542512395044658348032, coefficient := (-36790030542512395044658348032) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 36790030542512395044658348032, coefficient := (-36790030542512395044658348032) }, { argument := 36732002103170892844272451584, coefficient := (-36732002103170892844272451584) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 43579357945468152489808232448, coefficient := (-43579357945468152489808232448) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 102145431389159778848788709376, coefficient := (-102145431389159778848788709376) }, { argument := 2332022394589149299256663736320, coefficient := (-2332022394589149299256663736320) }, { argument := 70733124749411361908762607616, coefficient := (-70733124749411361908762607616) }, { argument := 91209837159150442685273210880, coefficient := (-91209837159150442685273210880) }, { argument := 1221096749958505076249797328896, coefficient := (-1221096749958505076249797328896) }, { argument := 2135236393017789733348535435264, coefficient := (-2135236393017789733348535435264) }, { argument := 2330165734594254055703465426944, coefficient := (-2330165734594254055703465426944) }, { argument := 1221096749958505076249797328896, coefficient := (-1221096749958505076249797328896) }, { argument := 68880823498809643385627869184, coefficient := (-68880823498809643385627869184) }, { argument := 70737733779098642682491174912, coefficient := (-70737733779098642682491174912) }, { argument := 70733124749411361908762607616, coefficient := (-70733124749411361908762607616) }, { argument := 68876214469122362611899301888, coefficient := (-68876214469122362611899301888) }, { argument := 2135236393017789733348535435264, coefficient := (-2135236393017789733348535435264) }, { argument := 68876214469122362611899301888, coefficient := (-68876214469122362611899301888) }, { argument := 102145181103766023105123713024, coefficient := (-102145181103766023105123713024) }, { argument := 91209837159150442685273210880, coefficient := (-91209837159150442685273210880) }, { argument := 61981604083286237830161891328, coefficient := (-61981604083286237830161891328) }, { argument := 5116932770341519923039342428160, coefficient := (-5116932770341519923039342428160) }, { argument := 731613179617203863448409079808, coefficient := (-731613179617203863448409079808) }, { argument := 45823014466272634800792036966400, coefficient := (-45823014466272634800792036966400) }, { argument := 463046316213420166739499417600, coefficient := (-463046316213420166739499417600) }, { argument := 27782778972805210004369965056, coefficient := (-27782778972805210004369965056) }, { argument := 731613179617203863448409079808, coefficient := (-731613179617203863448409079808) }, { argument := 726982716455069661781014085632, coefficient := (-726982716455069661781014085632) }, { argument := 463046316213420166739499417600, coefficient := (-463046316213420166739499417600) }, { argument := 11219612241851170640098070888448, coefficient := (-11219612241851170640098070888448) }, { argument := 717721790130801258446224097280, coefficient := (-717721790130801258446224097280) }, { argument := 5116938411703530769578624811008, coefficient := (-5116938411703530769578624811008) }, { argument := 731613179617203863448409079808, coefficient := (-731613179617203863448409079808) }, { argument := 27782778972805210004369965056, coefficient := (-27782778972805210004369965056) }, { argument := 717721790130801258446224097280, coefficient := (-717721790130801258446224097280) }, { argument := 27782778972805210004369965056, coefficient := (-27782778972805210004369965056) }, { argument := 731613179617203863448409079808, coefficient := (-731613179617203863448409079808) }, { argument := 731613179617203863448409079808, coefficient := (-731613179617203863448409079808) }, { argument := 61981604083286237830161891328, coefficient := (-61981604083286237830161891328) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 177183190437269088417873920, coefficient := (-177183190437269088417873920) }, { argument := 3255108327176114967219798016, coefficient := (-3255108327176114967219798016) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 192370321046177867425120256, coefficient := (-192370321046177867425120256) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 5887544299386969995142496256, coefficient := (-5887544299386969995142496256) }, { argument := 187307944176541607756038144, coefficient := (-187307944176541607756038144) }, { argument := 237931712872904204446859264, coefficient := (-237931712872904204446859264) }, { argument := 242994089742540464115941376, coefficient := (-242994089742540464115941376) }, { argument := 177223219871909038144880640, coefficient := (-177223219871909038144880640) }, { argument := 29043472517503188799900876800, coefficient := (-29043472517503188799900876800) }, { argument := 299013794868903358701030604800, coefficient := (-299013794868903358701030604800) }] }

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
def constantNumerator : ℤ := (-14124754712752872950636111714058240)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    196806225, 4803645, 327495830484561, 2645729385, 12070003655943307, 27683363565,
    1226069715, 12070001866544119, 1226069715, 2387609445, 45106459515, 2387609445,
    27683363565, 45106459515, 327496795001133, 2387609445, 2387609445, 2645729385,
    3980163, 163068015, 3357696705, 163068015, 3980163, 83549349,
    13079181999, 3269796699, 334202193, 13716685542061, 145565, 120611,
    12532110295439, 811005, 13715397568279, 3248179, 3248179, 2324881,
    120611, 181446702953929, 4142504786102839, 479306183, 1236123501, 1034308933,
    28937842319, 1034801674052251, 1034308933, 933509009, 479337415, 479306183,
    933446545, 28937842319, 933446545, 45361564589413, 1236123501, 100599714125133,
    2057692389556665, 73665049815, 588561958744222665, 23311724625, 2797406955, 73665049815,
    146397630645, 23311724625, 2259372350655, 144532692675
  ]
def negativeCoefficients : Array ℕ := #[
    29043472517503188799900876800, 177223219871909038144880640, 184363762516957505508744364032, 12201273213346991666406359040, 6794807995908350226607357558784, 127666980695752668899715317760,
    11308497124565504471303454720, 6794806988566160689873842864128, 11308497124565504471303454720, 11010905094971675406269153280, 416033657372173032917953413120, 11010905094971675406269153280,
    127666980695752668899715317760, 416033657372173032917953413120, 184364305491516786992266346496, 11010905094971675406269153280, 11010905094971675406269153280, 12201273213346991666406359040,
    9177631029081003761074176, 1504036969656415134280581120, 15484642948568209647017656320, 1504036969656415134280581120, 9177631029081003761074176, 12329707668224328420789583872,
    482536646058043793300697120768, 482536823036106436470135324672, 12329884646286971590227787776, 61774459895984189537838432256, 171852819269729976382914560, 8899520997896730919829504,
    225758429026820147749087870976, 239366426839981038533345280, 61768659377739511369390096384, 239673306874391270634029056, 239673306874391270634029056, 171545939235319744282230784,
    8899520997896730919829504, 102145412976364965030262734848, 2332022876384155244659126304768, 70733107925980766685651533824, 91209815465779412002840510464, 1221096459532966379766616686592,
    2135235885215818872271998550016, 2330166216832041531570019893248, 1221096459532966379766616686592, 68880807118100905931546034176, 70737716955668047459380101120, 70733107925980766685651533824,
    68876198088413625157817466880, 2135235885215818872271998550016, 68876198088413625157817466880, 102145162690911536591535079424, 91209815465779412002840510464, 226530417523763700904948137984,
    18534045357701003977850282311680, 2717760642228740303267907502080, 165665463630308152122865342218240, 1720101672296671078017662976000, 103206100337800264681059778560, 2717760642228740303267907502080,
    2700559625505773592487730872320, 1720101672296671078017662976000, 41678063519748340220367973908480, 2666157592059840170927377612800
  ]
def negativeScales : Array ℕ := #[
    27, 22, 48, 31, 53, 34,
    30, 53, 30, 31, 35, 31,
    34, 35, 48, 31, 31, 31,
    21, 27, 31, 27, 21, 26,
    33, 31, 28, 43, 17, 16,
    43, 19, 43, 21, 21, 21,
    16, 47, 51, 28, 30, 29,
    34, 49, 29, 29, 28, 28,
    29, 34, 29, 45, 30, 46,
    50, 36, 59, 34, 31, 36,
    37, 34, 41, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    27552200613083350, 22195698105949777, 48218469867508158, 31301018358957216, 53422275631275875, 34688300191893513,
    30191393867782718, 53422275417393792, 30191393867782718, 31152919719968082, 35392614999714574, 31152919719968082,
    34688300191893513, 35392614999714574, 48218474116420958, 31152919719968082, 31152919719968082, 31301018358957216,
    21924396090852929, 27280898591264535, 31644824773989832, 27280898591264535, 21924396090852929, 26316125251347425,
    33606553263195809, 31606553792327283, 28316145959343734, 43640997148758011, 17151303986591323, 16880001967812042,
    43510694605611344, 19629351283408454, 43640861675751256, 21631199707801444, 21631199707801444, 21148725442489547,
    16880001967812042, 47366539170441578, 51879424790602762, 28836372311124385, 30203175743975523, 29946020025727397,
    34752238303884453, 49878275719313234, 29946020025727397, 29798088705232114, 28836466315304446, 28836372311124385,
    29797992166775140, 34752238303884453, 29797992166775140, 45366535635422097, 30203175743975523, 46515619533856838,
    50869948751490144, 36100261247731467, 59029971910877150, 34440336689329121, 31381443000275523, 36100261247731467,
    37091101248445991, 34440336689329121, 41039059189005710, 37072604904828601
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
noncomputable def negativeCeiling : ℝ := 687539081 / 4000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 29043472517503188799900876800, coefficient := (-29043472517503188799900876800) }, { argument := 177223219871909038144880640, coefficient := (-177223219871909038144880640) }, { argument := 184363762516957505508744364032, coefficient := (-184363762516957505508744364032) }, { argument := 12201273213346991666406359040, coefficient := (-12201273213346991666406359040) }, { argument := 6794807995908350226607357558784, coefficient := (-6794807995908350226607357558784) }, { argument := 127666980695752668899715317760, coefficient := (-127666980695752668899715317760) }, { argument := 11308497124565504471303454720, coefficient := (-11308497124565504471303454720) }, { argument := 6794806988566160689873842864128, coefficient := (-6794806988566160689873842864128) }, { argument := 11308497124565504471303454720, coefficient := (-11308497124565504471303454720) }, { argument := 11010905094971675406269153280, coefficient := (-11010905094971675406269153280) }, { argument := 416033657372173032917953413120, coefficient := (-416033657372173032917953413120) }, { argument := 11010905094971675406269153280, coefficient := (-11010905094971675406269153280) }, { argument := 127666980695752668899715317760, coefficient := (-127666980695752668899715317760) }, { argument := 416033657372173032917953413120, coefficient := (-416033657372173032917953413120) }, { argument := 184364305491516786992266346496, coefficient := (-184364305491516786992266346496) }, { argument := 11010905094971675406269153280, coefficient := (-11010905094971675406269153280) }, { argument := 11010905094971675406269153280, coefficient := (-11010905094971675406269153280) }, { argument := 12201273213346991666406359040, coefficient := (-12201273213346991666406359040) }, { argument := 9177631029081003761074176, coefficient := (-9177631029081003761074176) }, { argument := 1504036969656415134280581120, coefficient := (-1504036969656415134280581120) }, { argument := 15484642948568209647017656320, coefficient := (-15484642948568209647017656320) }, { argument := 1504036969656415134280581120, coefficient := (-1504036969656415134280581120) }, { argument := 9177631029081003761074176, coefficient := (-9177631029081003761074176) }, { argument := 12329707668224328420789583872, coefficient := (-12329707668224328420789583872) }, { argument := 482536646058043793300697120768, coefficient := (-482536646058043793300697120768) }, { argument := 482536823036106436470135324672, coefficient := (-482536823036106436470135324672) }, { argument := 12329884646286971590227787776, coefficient := (-12329884646286971590227787776) }, { argument := 61774459895984189537838432256, coefficient := (-61774459895984189537838432256) }, { argument := 171852819269729976382914560, coefficient := (-171852819269729976382914560) }, { argument := 8899520997896730919829504, coefficient := (-8899520997896730919829504) }, { argument := 225758429026820147749087870976, coefficient := (-225758429026820147749087870976) }, { argument := 239366426839981038533345280, coefficient := (-239366426839981038533345280) }, { argument := 61768659377739511369390096384, coefficient := (-61768659377739511369390096384) }, { argument := 239673306874391270634029056, coefficient := (-239673306874391270634029056) }, { argument := 239673306874391270634029056, coefficient := (-239673306874391270634029056) }, { argument := 171545939235319744282230784, coefficient := (-171545939235319744282230784) }, { argument := 8899520997896730919829504, coefficient := (-8899520997896730919829504) }, { argument := 102145412976364965030262734848, coefficient := (-102145412976364965030262734848) }, { argument := 2332022876384155244659126304768, coefficient := (-2332022876384155244659126304768) }, { argument := 70733107925980766685651533824, coefficient := (-70733107925980766685651533824) }, { argument := 91209815465779412002840510464, coefficient := (-91209815465779412002840510464) }, { argument := 1221096459532966379766616686592, coefficient := (-1221096459532966379766616686592) }, { argument := 2135235885215818872271998550016, coefficient := (-2135235885215818872271998550016) }, { argument := 2330166216832041531570019893248, coefficient := (-2330166216832041531570019893248) }, { argument := 1221096459532966379766616686592, coefficient := (-1221096459532966379766616686592) }, { argument := 68880807118100905931546034176, coefficient := (-68880807118100905931546034176) }, { argument := 70737716955668047459380101120, coefficient := (-70737716955668047459380101120) }, { argument := 70733107925980766685651533824, coefficient := (-70733107925980766685651533824) }, { argument := 68876198088413625157817466880, coefficient := (-68876198088413625157817466880) }, { argument := 2135235885215818872271998550016, coefficient := (-2135235885215818872271998550016) }, { argument := 68876198088413625157817466880, coefficient := (-68876198088413625157817466880) }, { argument := 102145162690911536591535079424, coefficient := (-102145162690911536591535079424) }, { argument := 91209815465779412002840510464, coefficient := (-91209815465779412002840510464) }, { argument := 226530417523763700904948137984, coefficient := (-226530417523763700904948137984) }, { argument := 18534045357701003977850282311680, coefficient := (-18534045357701003977850282311680) }, { argument := 2717760642228740303267907502080, coefficient := (-2717760642228740303267907502080) }, { argument := 165665463630308152122865342218240, coefficient := (-165665463630308152122865342218240) }, { argument := 1720101672296671078017662976000, coefficient := (-1720101672296671078017662976000) }, { argument := 103206100337800264681059778560, coefficient := (-103206100337800264681059778560) }, { argument := 2717760642228740303267907502080, coefficient := (-2717760642228740303267907502080) }, { argument := 2700559625505773592487730872320, coefficient := (-2700559625505773592487730872320) }, { argument := 1720101672296671078017662976000, coefficient := (-1720101672296671078017662976000) }, { argument := 41678063519748340220367973908480, coefficient := (-41678063519748340220367973908480) }, { argument := 2666157592059840170927377612800, coefficient := (-2666157592059840170927377612800) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk18
