import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 17, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17

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
def constantNumerator : ℤ := (-8428632514805358977960762734018560)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    35103811185, 365881153275, 35103811185, 475356195, 3527623827, 132541889389,
    265063729931, 7075296501, 5548905, 409772115, 4270986225, 409772115,
    5548905, 3527623827, 132541889389, 265063729931, 7075296501, 12169489617,
    22131528495, 12169489617, 185040345, 15493268007, 7746636807, 92517369,
    184346955, 13613540265, 141891653475, 13613540265, 184346955, 116295291,
    4369512837, 8738364723, 233251533, 475356195, 35103811185, 365881153275,
    35103811185, 475356195, 43533203931, 1635654305317, 3271061194643, 87313823853,
    143703547605, 261340389675, 143703547605, 1744429365, 65542692555, 131075470845,
    3498772995, 10098087129, 18364459815, 10098087129, 2597, 2597,
    1488721489305, 122495814189549, 1776266583, 4378228373425959, 58558239, 136635891,
    1776266583, 1776266583, 58558239, 21920300799
  ]
def negativeCoefficients : Array ℕ := #[
    1295102041883035644918151249920, 13498631991715244705290439884800, 1295102041883035644918151249920, 8768774073017371991337861120, 65073173924988858558087954432, 2444966312604802653200658202624,
    2444781394630011673439264309248, 65258091899779838319481847808, 204718460848654599019560960, 30235845335790715445559951360, 315143159339655518411449958400, 30235845335790715445559951360,
    204718460848654599019560960, 65073173924988858558087954432, 2444966312604802653200658202624, 2444781394630011673439264309248, 65258091899779838319481847808, 56121865118116167766159392768,
    204127321053637660971588648960, 56121865118116167766159392768, 426673985940740107602493440, 35725043723815130732810993664, 35725056652676883393992982528, 426661057078987446420504576,
    1700300549826325697412464640, 251125493205595108839511818240, 2617439017848805555695098265600, 251125493205595108839511818240, 1700300549826325697412464640, 34324311520873244074595844096,
    1289652560494840959930017513472, 1289555021343302860715216338944, 34421850672411343289397018624, 8768774073017371991337861120, 1295102041883035644918151249920, 13498631991715244705290439884800,
    1295102041883035644918151249920, 8768774073017371991337861120, 803045871623763606161898602496, 30172496363243883291696034742272, 30170214353511023178816415596544, 805327881356623719041517748224,
    662715641288393044898265169920, 2410439642229125571047482982400, 662715641288393044898265169920, 64358084101637332639867207680, 2418098550927826799868782837760, 2417915665018692863841030635520,
    64540970010771268667619409920, 1490214631221467603663126003712, 5420231844147655338139204976640, 1490214631221467603663126003712, 50233285656627071467391025152, 50233285656627071467391025152,
    3352302772246223923068272640, 275836051569249196436097073152, 65532670126567130766828896256, 2464723458888010220494764638208, 34566683143683761283602055168, 2520487312560274260262649856,
    65532670126567130766828896256, 65532670126567130766828896256, 34566683143683761283602055168, 808716357715767998364273082368
  ]
def negativeScales : Array ℕ := #[
    35, 38, 35, 28, 31, 36,
    37, 32, 22, 28, 31, 28,
    22, 31, 36, 37, 32, 33,
    34, 33, 27, 33, 32, 26,
    27, 33, 37, 33, 27, 26,
    32, 33, 27, 28, 35, 38,
    35, 28, 35, 40, 41, 36,
    37, 37, 37, 30, 35, 36,
    31, 33, 34, 33, 11, 11,
    40, 46, 30, 51, 25, 27,
    30, 30, 25, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    35030908619836850, 38412584147393805, 35030908619836850, 28824433722398829, 31716049579426571, 36947657444119108,
    37947548325896033, 32720143461630567, 22403771672871506, 28610246571371618, 31991922119724051, 28610246571371618,
    22403771672871506, 31716049579426571, 36947657444119108, 37947548325896033, 32720143461630567, 33502549612203830,
    34365384041946861, 33502549612203830, 27463264620032912, 33850922435642992, 32850922957752975, 26463220903546899,
    27457848345627353, 33664323244150467, 37045998771676865, 33664323244150467, 27457848345627353, 26793217440406159,
    32024825294622351, 33024716176417771, 27797311322649096, 28824433722398829, 35030908619836850, 38412584147393805,
    35030908619836850, 28824433722398829, 35341397151523362, 40573005006304426, 41572895888099839, 36345491033717029,
    37064304721763366, 37927139158555348, 37064304721763366, 30700108035525006, 35931715897860371, 36931606779641439,
    31704201917725985, 33233362979388147, 34096197409131470, 33233362979388147, 11342630298678409, 11342630298678409,
    40437211017765709, 46799725780732898, 30726200972467971, 51959268644603931, 25803368833549807, 27025761254194400,
    30726200972467971, 30726200972467971, 25803368833549807, 34351548544537397
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
noncomputable def negativeCeiling : ℝ := 12367493961 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 13498631991715244705290439884800, coefficient := (-13498631991715244705290439884800) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 56121865118116167766159392768, coefficient := (-56121865118116167766159392768) }, { argument := 204127321053637660971588648960, coefficient := (-204127321053637660971588648960) }, { argument := 56121865118116167766159392768, coefficient := (-56121865118116167766159392768) }, { argument := 426673985940740107602493440, coefficient := (-426673985940740107602493440) }, { argument := 35725043723815130732810993664, coefficient := (-35725043723815130732810993664) }, { argument := 35725056652676883393992982528, coefficient := (-35725056652676883393992982528) }, { argument := 426661057078987446420504576, coefficient := (-426661057078987446420504576) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 2617439017848805555695098265600, coefficient := (-2617439017848805555695098265600) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 1700300549826325697412464640, coefficient := (-1700300549826325697412464640) }, { argument := 34324311520873244074595844096, coefficient := (-34324311520873244074595844096) }, { argument := 1289652560494840959930017513472, coefficient := (-1289652560494840959930017513472) }, { argument := 1289555021343302860715216338944, coefficient := (-1289555021343302860715216338944) }, { argument := 34421850672411343289397018624, coefficient := (-34421850672411343289397018624) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 13498631991715244705290439884800, coefficient := (-13498631991715244705290439884800) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 8768774073017371991337861120, coefficient := (-8768774073017371991337861120) }, { argument := 803045871623763606161898602496, coefficient := (-803045871623763606161898602496) }, { argument := 30172496363243883291696034742272, coefficient := (-30172496363243883291696034742272) }, { argument := 30170214353511023178816415596544, coefficient := (-30170214353511023178816415596544) }, { argument := 805327881356623719041517748224, coefficient := (-805327881356623719041517748224) }, { argument := 662715641288393044898265169920, coefficient := (-662715641288393044898265169920) }, { argument := 2410439642229125571047482982400, coefficient := (-2410439642229125571047482982400) }, { argument := 662715641288393044898265169920, coefficient := (-662715641288393044898265169920) }, { argument := 64358084101637332639867207680, coefficient := (-64358084101637332639867207680) }, { argument := 2418098550927826799868782837760, coefficient := (-2418098550927826799868782837760) }, { argument := 2417915665018692863841030635520, coefficient := (-2417915665018692863841030635520) }, { argument := 64540970010771268667619409920, coefficient := (-64540970010771268667619409920) }, { argument := 1490214631221467603663126003712, coefficient := (-1490214631221467603663126003712) }, { argument := 5420231844147655338139204976640, coefficient := (-5420231844147655338139204976640) }, { argument := 1490214631221467603663126003712, coefficient := (-1490214631221467603663126003712) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 50233285656627071467391025152, coefficient := (-50233285656627071467391025152) }, { argument := 3352302772246223923068272640, coefficient := (-3352302772246223923068272640) }, { argument := 275836051569249196436097073152, coefficient := (-275836051569249196436097073152) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 2464723458888010220494764638208, coefficient := (-2464723458888010220494764638208) }, { argument := 34566683143683761283602055168, coefficient := (-34566683143683761283602055168) }, { argument := 2520487312560274260262649856, coefficient := (-2520487312560274260262649856) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 34566683143683761283602055168, coefficient := (-34566683143683761283602055168) }, { argument := 808716357715767998364273082368, coefficient := (-808716357715767998364273082368) }] }

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
def constantNumerator : ℤ := (-2149679396657500566292198523404288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    878373585, 122495814189549, 1776266583, 136635891, 878373585, 136635891,
    1776266583, 1776266583, 6594220403469, 15261413601859, 865074465, 510914116340157,
    13613540265, 409772115, 4087274153630251, 409772115, 409772115, 35103811185,
    409772115, 13613540265, 35103811185, 122130085905877, 409772115, 409772115,
    865074465, 818177739804825, 7746636807, 435204315, 2951043236131875, 23530046631,
    204544370185425, 23530046631, 23530046631, 7746636807, 435204315, 3527623827,
    132541889389, 265063729931, 7075296501, 143703547605, 261340389675, 143703547605,
    14909429, 14909429, 1294626555, 2354417925, 1294626555, 1127,
    1127, 10395525, 870408315, 435204315, 5197605, 5548905,
    409772115, 4270986225, 409772115, 5548905, 271355679, 10195529953,
    20389517687, 544253577, 5548905, 409772115
  ]
def negativeCoefficients : Array ℕ := #[
    64812530894407052406753853440, 275836051569249196436097073152, 65532670126567130766828896256, 2520487312560274260262649856, 64812530894407052406753853440, 2520487312560274260262649856,
    65532670126567130766828896256, 65532670126567130766828896256, 3712216068982738773583331328, 274925186441916846401709408256, 31915614521112421859202170880, 9203810495871429227076007231488,
    251125493205595108839511818240, 30235845335790715445559951360, 9203723177625128912169885237248, 30235845335790715445559951360, 30235845335790715445559951360, 1295102041883035644918151249920,
    30235845335790715445559951360, 251125493205595108839511818240, 1295102041883035644918151249920, 275012504688217161307831402496, 30235845335790715445559951360, 30235845335790715445559951360,
    31915614521112421859202170880, 921186241026961125671750860800, 35725056652676883393992982528, 2007025654644768729999605760, 3322579304649433721906135040000, 54256593530563581334322675712,
    921185949347812821812694220800, 54256593530563581334322675712, 54256593530563581334322675712, 35725056652676883393992982528, 2007025654644768729999605760, 65073173924988858558087954432,
    2444966312604802653200658202624, 2444781394630011673439264309248, 65258091899779838319481847808, 662715641288393044898265169920, 2410439642229125571047482982400, 662715641288393044898265169920,
    70407787788324691568790339584, 70407787788324691568790339584, 47763289462226525758433525760, 173725379620117158273692467200, 47763289462226525758433525760, 43598700758581986556603531264,
    43598700758581986556603531264, 23970448648356185820364800, 2007024928304220827686010880, 2007025654644768729999605760, 23969722307808283506769920, 204718460848654599019560960,
    30235845335790715445559951360, 315143159339655518411449958400, 30235845335790715445559951360, 204718460848654599019560960, 2502814381730340713772613632, 94037165869415486661563777024,
    94030053639615833593817858048, 2509926611529993781518532608, 204718460848654599019560960, 30235845335790715445559951360
  ]
def negativeScales : Array ℕ := #[
    29, 46, 30, 27, 29, 27,
    30, 30, 42, 43, 29, 48,
    33, 28, 51, 28, 28, 35,
    28, 33, 35, 46, 28, 28,
    29, 49, 32, 28, 51, 34,
    47, 34, 34, 32, 28, 31,
    36, 37, 32, 37, 37, 37,
    23, 23, 30, 31, 30, 10,
    10, 23, 29, 28, 22, 22,
    28, 31, 28, 22, 28, 33,
    34, 29, 22, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29710259428558445, 46799725780732898, 30726200972467971, 27025761254194400, 29710259428558445, 27025761254194400,
    30726200972467971, 30726200972467971, 42584339246721516, 43794953833377221, 29688249083420169, 48860074127859730,
    33664323244150467, 28610246571371618, 51860060440680542, 28610246571371618, 28610246571371618, 35030908619836850,
    28610246571371618, 33664323244150467, 35030908619836850, 46795411971109987, 28610246571371618, 28610246571371618,
    29688249083420169, 49539407614721056, 32850922957752975, 28697117619978681, 51390146481354538, 34453785128519857,
    47539407157914269, 34453785128519857, 34453785128519857, 32850922957752975, 28697117619978681, 31716049579426571,
    36947657444119108, 37947548325896033, 32720143461630567, 37064304721763366, 37927139158555348, 37064304721763366,
    23829721671853330, 23829721671853330, 30269888855413261, 31132723285156585, 30269888855413261, 10138271800172222,
    10138271800172222, 23309459283953801, 29697117097868714, 28697117619978681, 22309415567467788, 22403771672871506,
    28610246571371618, 31991922119724051, 28610246571371618, 22403771672871506, 28015609861180364, 33247217715958799,
    34247108597754219, 29019703743374031, 22403771672871506, 28610246571371618
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
noncomputable def negativeCeiling : ℝ := 5168955773 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 64812530894407052406753853440, coefficient := (-64812530894407052406753853440) }, { argument := 275836051569249196436097073152, coefficient := (-275836051569249196436097073152) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 2520487312560274260262649856, coefficient := (-2520487312560274260262649856) }, { argument := 64812530894407052406753853440, coefficient := (-64812530894407052406753853440) }, { argument := 2520487312560274260262649856, coefficient := (-2520487312560274260262649856) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 65532670126567130766828896256, coefficient := (-65532670126567130766828896256) }, { argument := 3712216068982738773583331328, coefficient := (-3712216068982738773583331328) }, { argument := 274925186441916846401709408256, coefficient := (-274925186441916846401709408256) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 9203810495871429227076007231488, coefficient := (-9203810495871429227076007231488) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 9203723177625128912169885237248, coefficient := (-9203723177625128912169885237248) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 251125493205595108839511818240, coefficient := (-251125493205595108839511818240) }, { argument := 1295102041883035644918151249920, coefficient := (-1295102041883035644918151249920) }, { argument := 275012504688217161307831402496, coefficient := (-275012504688217161307831402496) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 31915614521112421859202170880, coefficient := (-31915614521112421859202170880) }, { argument := 921186241026961125671750860800, coefficient := (-921186241026961125671750860800) }, { argument := 35725056652676883393992982528, coefficient := (-35725056652676883393992982528) }, { argument := 2007025654644768729999605760, coefficient := (-2007025654644768729999605760) }, { argument := 3322579304649433721906135040000, coefficient := (-3322579304649433721906135040000) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 921185949347812821812694220800, coefficient := (-921185949347812821812694220800) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 54256593530563581334322675712, coefficient := (-54256593530563581334322675712) }, { argument := 35725056652676883393992982528, coefficient := (-35725056652676883393992982528) }, { argument := 2007025654644768729999605760, coefficient := (-2007025654644768729999605760) }, { argument := 65073173924988858558087954432, coefficient := (-65073173924988858558087954432) }, { argument := 2444966312604802653200658202624, coefficient := (-2444966312604802653200658202624) }, { argument := 2444781394630011673439264309248, coefficient := (-2444781394630011673439264309248) }, { argument := 65258091899779838319481847808, coefficient := (-65258091899779838319481847808) }, { argument := 662715641288393044898265169920, coefficient := (-662715641288393044898265169920) }, { argument := 2410439642229125571047482982400, coefficient := (-2410439642229125571047482982400) }, { argument := 662715641288393044898265169920, coefficient := (-662715641288393044898265169920) }, { argument := 70407787788324691568790339584, coefficient := (-70407787788324691568790339584) }, { argument := 70407787788324691568790339584, coefficient := (-70407787788324691568790339584) }, { argument := 47763289462226525758433525760, coefficient := (-47763289462226525758433525760) }, { argument := 173725379620117158273692467200, coefficient := (-173725379620117158273692467200) }, { argument := 47763289462226525758433525760, coefficient := (-47763289462226525758433525760) }, { argument := 43598700758581986556603531264, coefficient := (-43598700758581986556603531264) }, { argument := 43598700758581986556603531264, coefficient := (-43598700758581986556603531264) }, { argument := 23970448648356185820364800, coefficient := (-23970448648356185820364800) }, { argument := 2007024928304220827686010880, coefficient := (-2007024928304220827686010880) }, { argument := 2007025654644768729999605760, coefficient := (-2007025654644768729999605760) }, { argument := 23969722307808283506769920, coefficient := (-23969722307808283506769920) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 315143159339655518411449958400, coefficient := (-315143159339655518411449958400) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 2502814381730340713772613632, coefficient := (-2502814381730340713772613632) }, { argument := 94037165869415486661563777024, coefficient := (-94037165869415486661563777024) }, { argument := 94030053639615833593817858048, coefficient := (-94030053639615833593817858048) }, { argument := 2509926611529993781518532608, coefficient := (-2509926611529993781518532608) }, { argument := 204718460848654599019560960, coefficient := (-204718460848654599019560960) }, { argument := 30235845335790715445559951360, coefficient := (-30235845335790715445559951360) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk17
