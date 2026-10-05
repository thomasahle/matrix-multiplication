import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 4, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10248443804190622571835789588561920)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    105737671711459, 1312209675, 960500080865639, 14809223475, 1312209675, 1920999890910287,
    1312209675, 1312209675, 54400463955, 337425345, 14809223475, 54400463955,
    105737908774627, 1312209675, 337425345, 1312209675, 8309525, 5353350975,
    56935138855, 2676683555, 8309525, 3568691049, 558658568699, 139664693399,
    14274969093, 25219355886967, 166782399, 4327687, 181147500875999, 268649493,
    50452710093875, 268649493, 279968059, 166782399, 8322475, 102163992556215,
    1401734788894025, 4586411775, 371871225, 79704399225, 144162078225, 1401734789252425,
    79704399225, 2355184425, 2355184425, 4586411775, 4586411775, 144162078225,
    4586411775, 102163992197815, 371871225, 128168372681337, 1927699753860861, 69753618011,
    33086097533417875, 2717673429, 4529455715, 138601344879, 4529455715, 2717673429,
    2220339191493, 142224909451, 1927699768022781, 138601344879
  ]
def negativeCoefficients : Array ℕ := #[
    238100069459375294222100856832, 24205996045770586770427084800, 8651415612551646150954097573888, 273181955373696622123391385600, 24205996045770586770427084800, 8651414392882331999245646692352,
    24205996045770586770427084800, 24205996045770586770427084800, 1003511436068946325825420001280, 24897595932792603535296430080, 273181955373696622123391385600, 1003511436068946325825420001280,
    238100603278172828256746602496, 24205996045770586770427084800, 24897595932792603535296430080, 24205996045770586770427084800, 76641840524545680945971200, 24687973843142125002581606400,
    262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200, 65830730459041073077822685184, 2576357910343834665309905616896, 2576358855264464783026404982784,
    65831675379671190794322051072, 56788940887534252920003362816, 192287014397019490483175424, 9978966815014983538049024, 203953954361061423534231781376, 309731777681426604430983168,
    56804701594651778065891328000, 309731777681426604430983168, 322781195824138505980739584, 192287014397019490483175424, 9595160399052868786585600, 57513214850856500139739054080,
    789106534116923983109344460800, 42302182115036477730796339200, 54878506527614890029141196800, 735143327026174464348703948800, 1329660481075335772997733580800, 789106534318685246415542681600,
    735143327026174464348703948800, 43445484334361787939736780800, 43445484334361787939736780800, 42302182115036477730796339200, 42302182115036477730796339200, 1329660481075335772997733580800,
    42302182115036477730796339200, 57513214649095236833540833280, 54878506527614890029141196800, 144304758862088043116560908288, 8681587893169970457505280557056, 2573454279328428182369103511552,
    74503268261322314338436907008000, 1604231239061877308489830760448, 83553710367806109817178685440, 2556743537254866960405667774464, 2673718731769795514149717934080, 1604231239061877308489830760448,
    40958028822298555032380991602688, 2623586505549111848259410722816, 8681587956949588092356055269376, 2556743537254866960405667774464
  ]
def negativeScales : Array ℕ := #[
    46, 30, 49, 33, 30, 50,
    30, 30, 35, 28, 33, 35,
    46, 30, 28, 30, 22, 32,
    35, 31, 22, 31, 39, 37,
    33, 44, 27, 22, 47, 28,
    45, 28, 28, 27, 22, 46,
    50, 32, 28, 36, 37, 50,
    36, 31, 31, 32, 32, 37,
    32, 46, 28, 46, 50, 36,
    54, 31, 32, 37, 32, 31,
    41, 37, 50, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    46587482793213785, 30289351117321641, 49770779064127883, 33785776943923195, 30289351117321641, 50770778860737931,
    30289351117321641, 30289351117321641, 35662899904472902, 28329993101818988, 33785776943923195, 35662899904472902,
    46587486027723000, 30289351117321641, 28329993101818988, 30289351117321641, 22986334598453789, 32317795095335792,
    35728600269470391, 31317799443612136, 22986334598453789, 31732747863016575, 39023175874704670, 37023176403836144,
    33732768571012956, 44519596662630384, 27313391804384731, 22045164729330614, 47364158230826622, 28001149874467302,
    45519997000072670, 28001149874467302, 28060687001444666, 27313391804384731, 22988581220676475, 46537880140023032,
    50316134837608171, 32094718742067114, 28470227877159418, 36213940303766112, 37068900757911383, 50316134837977044,
    36213940303766112, 31133192889881750, 31133192889881750, 32094718742067114, 32094718742067114, 37068900757911383,
    32094718742067114, 46537880134961934, 28470227877159418, 46865033631643263, 50775801787848568, 36021548998090098,
    54877074658565518, 31339724958116353, 32076690552282559, 37012150300087848, 32076690552282559, 31339724958116353,
    41013917226262036, 37049383206286824, 50775801798447382, 37012150300087848
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
noncomputable def negativeCeiling : ℝ := 26140362189 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 238100069459375294222100856832, coefficient := (-238100069459375294222100856832) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 8651415612551646150954097573888, coefficient := (-8651415612551646150954097573888) }, { argument := 273181955373696622123391385600, coefficient := (-273181955373696622123391385600) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 8651414392882331999245646692352, coefficient := (-8651414392882331999245646692352) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 1003511436068946325825420001280, coefficient := (-1003511436068946325825420001280) }, { argument := 24897595932792603535296430080, coefficient := (-24897595932792603535296430080) }, { argument := 273181955373696622123391385600, coefficient := (-273181955373696622123391385600) }, { argument := 1003511436068946325825420001280, coefficient := (-1003511436068946325825420001280) }, { argument := 238100603278172828256746602496, coefficient := (-238100603278172828256746602496) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 24897595932792603535296430080, coefficient := (-24897595932792603535296430080) }, { argument := 24205996045770586770427084800, coefficient := (-24205996045770586770427084800) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 65830730459041073077822685184, coefficient := (-65830730459041073077822685184) }, { argument := 2576357910343834665309905616896, coefficient := (-2576357910343834665309905616896) }, { argument := 2576358855264464783026404982784, coefficient := (-2576358855264464783026404982784) }, { argument := 65831675379671190794322051072, coefficient := (-65831675379671190794322051072) }, { argument := 56788940887534252920003362816, coefficient := (-56788940887534252920003362816) }, { argument := 192287014397019490483175424, coefficient := (-192287014397019490483175424) }, { argument := 9978966815014983538049024, coefficient := (-9978966815014983538049024) }, { argument := 203953954361061423534231781376, coefficient := (-203953954361061423534231781376) }, { argument := 309731777681426604430983168, coefficient := (-309731777681426604430983168) }, { argument := 56804701594651778065891328000, coefficient := (-56804701594651778065891328000) }, { argument := 309731777681426604430983168, coefficient := (-309731777681426604430983168) }, { argument := 322781195824138505980739584, coefficient := (-322781195824138505980739584) }, { argument := 192287014397019490483175424, coefficient := (-192287014397019490483175424) }, { argument := 9595160399052868786585600, coefficient := (-9595160399052868786585600) }, { argument := 57513214850856500139739054080, coefficient := (-57513214850856500139739054080) }, { argument := 789106534116923983109344460800, coefficient := (-789106534116923983109344460800) }, { argument := 42302182115036477730796339200, coefficient := (-42302182115036477730796339200) }, { argument := 54878506527614890029141196800, coefficient := (-54878506527614890029141196800) }, { argument := 735143327026174464348703948800, coefficient := (-735143327026174464348703948800) }, { argument := 1329660481075335772997733580800, coefficient := (-1329660481075335772997733580800) }, { argument := 789106534318685246415542681600, coefficient := (-789106534318685246415542681600) }, { argument := 735143327026174464348703948800, coefficient := (-735143327026174464348703948800) }, { argument := 43445484334361787939736780800, coefficient := (-43445484334361787939736780800) }, { argument := 43445484334361787939736780800, coefficient := (-43445484334361787939736780800) }, { argument := 42302182115036477730796339200, coefficient := (-42302182115036477730796339200) }, { argument := 42302182115036477730796339200, coefficient := (-42302182115036477730796339200) }, { argument := 1329660481075335772997733580800, coefficient := (-1329660481075335772997733580800) }, { argument := 42302182115036477730796339200, coefficient := (-42302182115036477730796339200) }, { argument := 57513214649095236833540833280, coefficient := (-57513214649095236833540833280) }, { argument := 54878506527614890029141196800, coefficient := (-54878506527614890029141196800) }, { argument := 144304758862088043116560908288, coefficient := (-144304758862088043116560908288) }, { argument := 8681587893169970457505280557056, coefficient := (-8681587893169970457505280557056) }, { argument := 2573454279328428182369103511552, coefficient := (-2573454279328428182369103511552) }, { argument := 74503268261322314338436907008000, coefficient := (-74503268261322314338436907008000) }, { argument := 1604231239061877308489830760448, coefficient := (-1604231239061877308489830760448) }, { argument := 83553710367806109817178685440, coefficient := (-83553710367806109817178685440) }, { argument := 2556743537254866960405667774464, coefficient := (-2556743537254866960405667774464) }, { argument := 2673718731769795514149717934080, coefficient := (-2673718731769795514149717934080) }, { argument := 1604231239061877308489830760448, coefficient := (-1604231239061877308489830760448) }, { argument := 40958028822298555032380991602688, coefficient := (-40958028822298555032380991602688) }, { argument := 2623586505549111848259410722816, coefficient := (-2623586505549111848259410722816) }, { argument := 8681587956949588092356055269376, coefficient := (-8681587956949588092356055269376) }, { argument := 2556743537254866960405667774464, coefficient := (-2556743537254866960405667774464) }] }

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


end Parent2

namespace Parent2

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-10796650389178230077885577363980288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4529455715, 142224909451, 4529455715, 138601344879, 4529455715, 128168372681337,
    1845522479987341, 13955901715, 16470313685320265, 157502319355, 13955901715, 32940619367193825,
    13955901715, 13955901715, 578571811099, 3588660441, 157502319355, 578571811099,
    1845522507235981, 13955901715, 3588660441, 13955901715, 8309525, 5353350975,
    56935138855, 2676683555, 8309525, 139039911, 21765918261, 5441481561,
    556167627, 359435291170441, 29252065857, 759035641, 2643630110463777, 47118597099,
    718940998757325, 47118597099, 49103767237, 29252065857, 1459683925, 231733185,
    36276530435, 9069135935, 926946045, 36124867675, 129485789225, 9033841375,
    1144093417, 1144093975, 268649493, 47118597099, 11779650687, 67160961,
    8309525, 5353350975, 56935138855, 2676683555, 8309525, 279968059,
    49103767237, 12275943281, 69990543, 344489165
  ]
def negativeCoefficients : Array ℕ := #[
    83553710367806109817178685440, 2623586505549111848259410722816, 83553710367806109817178685440, 2556743537254866960405667774464, 2673718731769795514149717934080, 144304758862088043116560908288,
    2077873588293715647266799222784, 257440947254449217809615421440, 74175698575883526168697571901440, 2905404976157355458137088327680, 257440947254449217809615421440, 74175680553723727009885559193600,
    257440947254449217809615421440, 257440947254449217809615421440, 10672766127605880429764342185984, 264796402890290624032747290624, 2905404976157355458137088327680, 10672766127605880429764342185984,
    2077873618972956884854997254144, 257440947254449217809615421440, 264796402890290624032747290624, 257440947254449217809615421440, 76641840524545680945971200, 24687973843142125002581606400,
    262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200, 41037338467973655944616738816, 1606041294759793038115265839104, 1606041883801224799808668041216,
    41037927509405417638018940928, 809376321689501909331495354368, 33725335780711016635073298432, 1750217026543885094834143232, 2976462895097522318904391630848, 54324043862342895058890522624,
    809455603526215274448342220800, 54324043862342895058890522624, 56612789204746437105981325312, 33725335780711016635073298432, 1682900987061427975802060800, 2137361378540294580448788480,
    83647984102072554068503429120, 83648014781313791656701460480, 2137392057781532168646819840, 41649136793584249906973900800, 149286950938492054026164633600, 41661239961778349280329728000,
    2638099807476857596735913984, 2638101094137256737977139200, 309731777681426604430983168, 54324043862342895058890522624, 54324050375196474582969090048, 309725264827847080352415744,
    76641840524545680945971200, 24687973843142125002581606400, 262566983814825419049187409920, 24688048252696032328485437440, 76641840524545680945971200, 322781195824138505980739584,
    56612789204746437105981325312, 56612795991995334726489473024, 322774408575240885472591872, 3177351731460450944360120320
  ]
def negativeScales : Array ℕ := #[
    32, 37, 32, 37, 32, 46,
    50, 33, 53, 37, 33, 54,
    33, 33, 39, 31, 37, 39,
    50, 33, 31, 33, 22, 32,
    35, 31, 22, 27, 34, 32,
    29, 48, 34, 29, 51, 35,
    49, 35, 35, 34, 30, 27,
    35, 33, 29, 35, 36, 33,
    30, 30, 28, 35, 33, 26,
    22, 32, 35, 31, 22, 28,
    35, 33, 26, 28
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32076690552282559, 37049383206286824, 32076690552282559, 37012150300087848, 32076690552282559, 46865033631643263,
    50712950734315452, 33700156291389040, 53870717552927727, 37196582117435885, 33700156291389040, 54870717202402077,
    33700156291389040, 33700156291389040, 39073705078438164, 31740798275997401, 37196582117435885, 39073705078438164,
    50712950755616453, 33700156291389040, 31740798275997401, 33700156291389040, 22986334598453789, 32317795095335792,
    35728600269470391, 31317799443612136, 22986334598453789, 27050923822889312, 34341351834730926, 32341352363862399,
    29050944530885622, 48352725395303718, 34767819464375381, 29499592388991193, 51231441756309437, 35455577534127671,
    49352866706468848, 35455577534127671, 35515114661105424, 34767819464375381, 30443008860624594, 27787889417559181,
    35078317428897131, 33078317958028605, 29787910125555707, 35072273251920271, 36914002823416988, 33072692435737115,
    30091557709197235, 30091558412831768, 28001149874467302, 35455577534127671, 33455577707090881, 26001119538024525,
    22986334598453789, 32317795095335792, 35728600269470391, 31317799443612136, 22986334598453789, 28060687001444666,
    35515114661105424, 33515114834068634, 26060656665001889, 28359883366566665
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
noncomputable def negativeCeiling : ℝ := 60659557397 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 83553710367806109817178685440, coefficient := (-83553710367806109817178685440) }, { argument := 2623586505549111848259410722816, coefficient := (-2623586505549111848259410722816) }, { argument := 83553710367806109817178685440, coefficient := (-83553710367806109817178685440) }, { argument := 2556743537254866960405667774464, coefficient := (-2556743537254866960405667774464) }, { argument := 2673718731769795514149717934080, coefficient := (-2673718731769795514149717934080) }, { argument := 144304758862088043116560908288, coefficient := (-144304758862088043116560908288) }, { argument := 2077873588293715647266799222784, coefficient := (-2077873588293715647266799222784) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 74175698575883526168697571901440, coefficient := (-74175698575883526168697571901440) }, { argument := 2905404976157355458137088327680, coefficient := (-2905404976157355458137088327680) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 74175680553723727009885559193600, coefficient := (-74175680553723727009885559193600) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 10672766127605880429764342185984, coefficient := (-10672766127605880429764342185984) }, { argument := 264796402890290624032747290624, coefficient := (-264796402890290624032747290624) }, { argument := 2905404976157355458137088327680, coefficient := (-2905404976157355458137088327680) }, { argument := 10672766127605880429764342185984, coefficient := (-10672766127605880429764342185984) }, { argument := 2077873618972956884854997254144, coefficient := (-2077873618972956884854997254144) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 264796402890290624032747290624, coefficient := (-264796402890290624032747290624) }, { argument := 257440947254449217809615421440, coefficient := (-257440947254449217809615421440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 41037338467973655944616738816, coefficient := (-41037338467973655944616738816) }, { argument := 1606041294759793038115265839104, coefficient := (-1606041294759793038115265839104) }, { argument := 1606041883801224799808668041216, coefficient := (-1606041883801224799808668041216) }, { argument := 41037927509405417638018940928, coefficient := (-41037927509405417638018940928) }, { argument := 809376321689501909331495354368, coefficient := (-809376321689501909331495354368) }, { argument := 33725335780711016635073298432, coefficient := (-33725335780711016635073298432) }, { argument := 1750217026543885094834143232, coefficient := (-1750217026543885094834143232) }, { argument := 2976462895097522318904391630848, coefficient := (-2976462895097522318904391630848) }, { argument := 54324043862342895058890522624, coefficient := (-54324043862342895058890522624) }, { argument := 809455603526215274448342220800, coefficient := (-809455603526215274448342220800) }, { argument := 54324043862342895058890522624, coefficient := (-54324043862342895058890522624) }, { argument := 56612789204746437105981325312, coefficient := (-56612789204746437105981325312) }, { argument := 33725335780711016635073298432, coefficient := (-33725335780711016635073298432) }, { argument := 1682900987061427975802060800, coefficient := (-1682900987061427975802060800) }, { argument := 2137361378540294580448788480, coefficient := (-2137361378540294580448788480) }, { argument := 83647984102072554068503429120, coefficient := (-83647984102072554068503429120) }, { argument := 83648014781313791656701460480, coefficient := (-83648014781313791656701460480) }, { argument := 2137392057781532168646819840, coefficient := (-2137392057781532168646819840) }, { argument := 41649136793584249906973900800, coefficient := (-41649136793584249906973900800) }, { argument := 149286950938492054026164633600, coefficient := (-149286950938492054026164633600) }, { argument := 41661239961778349280329728000, coefficient := (-41661239961778349280329728000) }, { argument := 2638099807476857596735913984, coefficient := (-2638099807476857596735913984) }, { argument := 2638101094137256737977139200, coefficient := (-2638101094137256737977139200) }, { argument := 309731777681426604430983168, coefficient := (-309731777681426604430983168) }, { argument := 54324043862342895058890522624, coefficient := (-54324043862342895058890522624) }, { argument := 54324050375196474582969090048, coefficient := (-54324050375196474582969090048) }, { argument := 309725264827847080352415744, coefficient := (-309725264827847080352415744) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 24687973843142125002581606400, coefficient := (-24687973843142125002581606400) }, { argument := 262566983814825419049187409920, coefficient := (-262566983814825419049187409920) }, { argument := 24688048252696032328485437440, coefficient := (-24688048252696032328485437440) }, { argument := 76641840524545680945971200, coefficient := (-76641840524545680945971200) }, { argument := 322781195824138505980739584, coefficient := (-322781195824138505980739584) }, { argument := 56612789204746437105981325312, coefficient := (-56612789204746437105981325312) }, { argument := 56612795991995334726489473024, coefficient := (-56612795991995334726489473024) }, { argument := 322774408575240885472591872, coefficient := (-322774408575240885472591872) }, { argument := 3177351731460450944360120320, coefficient := (-3177351731460450944360120320) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk4
