import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 2,
parent chunk 7, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-35360998406831654160785600841515008)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18199396293125491, 29093716071, 950775035, 570465021, 950775035, 14641935539,
    16543485609, 557469883711025, 2963219912845553, 57702491401, 6332314241139423, 1427829734029,
    45425365571, 405268256556506403, 23326539077, 23326539077, 789419190869, 42969940405,
    1427829734029, 789419190869, 11852784071182169, 45425365571, 42969940405, 57702491401,
    18516141, 2956049937, 117987732243, 2956049937, 74056113, 19159037541,
    719854258587, 1439599628973, 38426963283, 5334590877592395, 431986945, 140964161,
    9085826829536359, 1423283303, 5334590665792487, 2851113837, 1277771911, 431986945,
    140964161, 609530859, 22901640213, 45799816227, 1222525917, 134834653485,
    231431894739, 134834653485, 29790445950165, 22905, 29790258932523, 11565,
    163197077189825, 2671200297621093, 16950304665, 22431598003293167, 17393449885, 553931525,
    16950304665, 9638408535, 17393449885, 271537233555
  ]
def negativeCoefficients : Array ℕ := #[
    20490698591021986865202419728384, 4293474676119260723492985765888, 140309629938537932140293652480, 2693944894819928297093638127616, 140309629938537932140293652480, 4321536602106968309921044496384,
    2441387560930560019241109553152, 313827645068905740977884364800, 6672578047654033062119178502144, 266105772822418278073451413504, 228145664454307124599043301310464, 6584702421116435263817531785216,
    209487523285733538057823453184, 228145746151621601119383884660736, 215149348239402012059386249216, 215149348239402012059386249216, 3640553445208828783004877848576, 198163873378396590054697861120,
    6584702421116435263817531785216, 3640553445208828783004877848576, 6672524240784870855585958985728, 209487523285733538057823453184, 198163873378396590054697861120, 266105772822418278073451413504,
    170781257129860225384316928, 27264748328472121705387524096, 272061187565498703977524494336, 27264748328472121705387524096, 170761770450589360456728576, 176710931108710285270610608128,
    6639483639262162678657943863296, 6638981481068039267539948142592, 177213089302833696388606328832, 6006215372124789340455284244480, 31875010470394576079662612480, 1300164900766094550617817088,
    20459463161926400736186997932032, 26254942834825006086669467648, 6006215133659292653978950565888, 26296883638075525265721655296, 23570731426791778627329458176, 31875010470394576079662612480,
    1300164900766094550617817088, 5621929880500671156502659072, 211230347938693051685592367104, 211214372140599701546842718208, 5637905678594021295252307968, 1243630172552552345339040890880,
    4269164932744021006852999348224, 1243630172552552345339040890880, 134164241280363995651207331840, 216331608580258447239413760, 134163399027781172742385041408, 218456673497549787585576960,
    91871787002506242813224550400, 6015008332499156223799867736064, 1250711728506640466446972354560, 50511468204477934503338407100416, 1283410074349951328314867056640, 40872932304138577334868377600,
    1250711728506640466446972354560, 711189022092011245626709770240, 1283410074349951328314867056640, 20035911415488730609552478699520
  ]
def negativeScales : Array ℕ := #[
    54, 34, 29, 29, 29, 33,
    33, 48, 51, 35, 52, 40,
    35, 58, 34, 34, 39, 35,
    40, 39, 53, 35, 35, 35,
    24, 31, 36, 31, 26, 34,
    39, 40, 35, 52, 28, 27,
    53, 30, 52, 31, 30, 28,
    27, 29, 34, 35, 30, 36,
    37, 36, 44, 14, 44, 13,
    47, 51, 33, 54, 34, 29,
    33, 33, 34, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    54014740112613001, 34759988529358935, 29824528782330926, 29087563187108130, 29824528782330926, 33769387227423425,
    33945544191902317, 48985887215476827, 51396087121968246, 35747914560060976, 52491654274313917, 40376961089641713,
    35402779073797449, 58491654790932497, 34441253221612111, 34441253221612111, 39522000635496995, 35322608725113459,
    40376961089641713, 39522000635496995, 53396075488201546, 35402779073797449, 35322608725113459, 35747914560060976,
    24142280118086310, 31461023495342428, 36779845907568427, 31461023495342428, 26142115492646422, 34157306037625041,
    39388913892403480, 40388804774198901, 35161399919818708, 52244299054903454, 28686412472770720, 27070753174774239,
    53012539232056408, 30406575711319991, 52244298997623957, 31408878497189412, 30250983184608290, 28686412472770720,
    27070753174774239, 29183124021780773, 34414731876559219, 35414622758354640, 30187217903974440, 36972400386179081,
    37751796746862514, 36972400386179081, 44759914954088023, 14483374942405524, 44759905897148303, 13497477645523802,
    47213608547733065, 51246409582567008, 33980592170803813, 54316381918350302, 34017825059686990, 29045132405682725,
    33980592170803813, 33166147806644091, 34017825059686990, 37982359097483404
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
noncomputable def negativeCeiling : ℝ := 421939176243 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 20490698591021986865202419728384, coefficient := (-20490698591021986865202419728384) }, { argument := 4293474676119260723492985765888, coefficient := (-4293474676119260723492985765888) }, { argument := 140309629938537932140293652480, coefficient := (-140309629938537932140293652480) }, { argument := 2693944894819928297093638127616, coefficient := (-2693944894819928297093638127616) }, { argument := 140309629938537932140293652480, coefficient := (-140309629938537932140293652480) }, { argument := 4321536602106968309921044496384, coefficient := (-4321536602106968309921044496384) }, { argument := 2441387560930560019241109553152, coefficient := (-2441387560930560019241109553152) }, { argument := 313827645068905740977884364800, coefficient := (-313827645068905740977884364800) }, { argument := 6672578047654033062119178502144, coefficient := (-6672578047654033062119178502144) }, { argument := 266105772822418278073451413504, coefficient := (-266105772822418278073451413504) }, { argument := 228145664454307124599043301310464, coefficient := (-228145664454307124599043301310464) }, { argument := 6584702421116435263817531785216, coefficient := (-6584702421116435263817531785216) }, { argument := 209487523285733538057823453184, coefficient := (-209487523285733538057823453184) }, { argument := 228145746151621601119383884660736, coefficient := (-228145746151621601119383884660736) }, { argument := 215149348239402012059386249216, coefficient := (-215149348239402012059386249216) }, { argument := 215149348239402012059386249216, coefficient := (-215149348239402012059386249216) }, { argument := 3640553445208828783004877848576, coefficient := (-3640553445208828783004877848576) }, { argument := 198163873378396590054697861120, coefficient := (-198163873378396590054697861120) }, { argument := 6584702421116435263817531785216, coefficient := (-6584702421116435263817531785216) }, { argument := 3640553445208828783004877848576, coefficient := (-3640553445208828783004877848576) }, { argument := 6672524240784870855585958985728, coefficient := (-6672524240784870855585958985728) }, { argument := 209487523285733538057823453184, coefficient := (-209487523285733538057823453184) }, { argument := 198163873378396590054697861120, coefficient := (-198163873378396590054697861120) }, { argument := 266105772822418278073451413504, coefficient := (-266105772822418278073451413504) }, { argument := 170781257129860225384316928, coefficient := (-170781257129860225384316928) }, { argument := 27264748328472121705387524096, coefficient := (-27264748328472121705387524096) }, { argument := 272061187565498703977524494336, coefficient := (-272061187565498703977524494336) }, { argument := 27264748328472121705387524096, coefficient := (-27264748328472121705387524096) }, { argument := 170761770450589360456728576, coefficient := (-170761770450589360456728576) }, { argument := 176710931108710285270610608128, coefficient := (-176710931108710285270610608128) }, { argument := 6639483639262162678657943863296, coefficient := (-6639483639262162678657943863296) }, { argument := 6638981481068039267539948142592, coefficient := (-6638981481068039267539948142592) }, { argument := 177213089302833696388606328832, coefficient := (-177213089302833696388606328832) }, { argument := 6006215372124789340455284244480, coefficient := (-6006215372124789340455284244480) }, { argument := 31875010470394576079662612480, coefficient := (-31875010470394576079662612480) }, { argument := 1300164900766094550617817088, coefficient := (-1300164900766094550617817088) }, { argument := 20459463161926400736186997932032, coefficient := (-20459463161926400736186997932032) }, { argument := 26254942834825006086669467648, coefficient := (-26254942834825006086669467648) }, { argument := 6006215133659292653978950565888, coefficient := (-6006215133659292653978950565888) }, { argument := 26296883638075525265721655296, coefficient := (-26296883638075525265721655296) }, { argument := 23570731426791778627329458176, coefficient := (-23570731426791778627329458176) }, { argument := 31875010470394576079662612480, coefficient := (-31875010470394576079662612480) }, { argument := 1300164900766094550617817088, coefficient := (-1300164900766094550617817088) }, { argument := 5621929880500671156502659072, coefficient := (-5621929880500671156502659072) }, { argument := 211230347938693051685592367104, coefficient := (-211230347938693051685592367104) }, { argument := 211214372140599701546842718208, coefficient := (-211214372140599701546842718208) }, { argument := 5637905678594021295252307968, coefficient := (-5637905678594021295252307968) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 4269164932744021006852999348224, coefficient := (-4269164932744021006852999348224) }, { argument := 1243630172552552345339040890880, coefficient := (-1243630172552552345339040890880) }, { argument := 134164241280363995651207331840, coefficient := (-134164241280363995651207331840) }, { argument := 216331608580258447239413760, coefficient := (-216331608580258447239413760) }, { argument := 134163399027781172742385041408, coefficient := (-134163399027781172742385041408) }, { argument := 218456673497549787585576960, coefficient := (-218456673497549787585576960) }, { argument := 91871787002506242813224550400, coefficient := (-91871787002506242813224550400) }, { argument := 6015008332499156223799867736064, coefficient := (-6015008332499156223799867736064) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 50511468204477934503338407100416, coefficient := (-50511468204477934503338407100416) }, { argument := 1283410074349951328314867056640, coefficient := (-1283410074349951328314867056640) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 711189022092011245626709770240, coefficient := (-711189022092011245626709770240) }, { argument := 1283410074349951328314867056640, coefficient := (-1283410074349951328314867056640) }, { argument := 20035911415488730609552478699520, coefficient := (-20035911415488730609552478699520) }] }

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


end Parent3

namespace Parent3

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-40311922423964065019569261867171840)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    332358915, 5342403277707927, 16950304665, 553931525, 332358915, 553931525,
    8530545485, 9638408535, 163197075475649, 23705696002775103, 115396254479, 405268256847961045,
    2855443488491, 90843859909, 50658550246452161, 46649549683, 46649549683, 1578718970851,
    85933380995, 2855443488491, 1578718970851, 23705504842265607, 90843859909, 85933380995,
    115396254479, 44852346549098217, 17242320355, 5626441379, 76218562444702717, 56808908117,
    44852344341543197, 113799314343, 51000968629, 17242320355, 5626441379, 313002333,
    11760301731, 23518824549, 627783579, 138359742465, 237482401791, 138359742465,
    520014210607915, 17815, 519998484436181, 8995, 4406361225, 7563133815,
    4406361225, 2845445, 2545, 2845445, 1285, 75,
    11565, 8995, 1285, 12079, 142635, 10023,
    8995, 142635, 1285, 10023
  ]
def negativeCoefficients : Array ℕ := #[
    784760300239460684829472849920, 6015011352687084124230226280448, 1250711728506640466446972354560, 40872932304138577334868377600, 784760300239460684829472849920, 40872932304138577334868377600,
    1258886314967468181913946030080, 711189022092011245626709770240, 91871786037510943457293631488, 6672560230291013148870671597568, 266085646679846568976615211008, 228145746315695978257709048791040,
    6584204406141735313187308306432, 209471679301155809619888570368, 228145828013051500585053486841856, 215133076039024885555561234432, 215133076039024885555561234432, 3640278102449815826637522993152,
    198148885825417657748543242240, 6584204406141735313187308306432, 3640278102449815826637522993152, 6672506423391054765135539208192, 209471679301155809619888570368, 198148885825417657748543242240,
    266085646679846568976615211008, 50499252801302770563654938001408, 318064670825597822186479943680, 12973690520517805904974839808, 171628944712339018459299568418816, 261984847285295048274653216768,
    50499250315816779195687976828928, 262403353431118203303845953536, 235200453952613126406318063616, 318064670825597822186479943680, 12973690520517805904974839808, 5773873931325013620191920128,
    216939276261360431460878647296, 216922868684940234021081710592, 5790281507745211059988856832, 1276143379678109269400192286720, 4380777087848439856705365344256, 1276143379678109269400192286720,
    2341935805121168622221095075840, 168257917784645458963988480, 2341864980740007415394154315776, 169910746053649834788782080, 40641508906946155076439244800, 139515193880523562315457495040,
    40641508906946155076439244800, 107497872774792141000681717760, 192294763182451953101701120, 107497872774792141000681717760, 194183709775599811187179520, 1450710983537555009647411200,
    218456673497549787585576960, 169910746053649834788782080, 194183709775599811187179520, 228165858986329778144935936, 2694298973136447380222115840, 6058531744998714109040001024,
    169910746053649834788782080, 2694298973136447380222115840, 194183709775599811187179520, 189329117031209815907500032
  ]
def negativeScales : Array ℕ := #[
    28, 52, 33, 29, 28, 29,
    32, 33, 47, 54, 36, 58,
    41, 36, 55, 35, 35, 40,
    36, 41, 40, 54, 36, 36,
    36, 55, 34, 32, 56, 35,
    55, 36, 35, 34, 32, 28,
    33, 34, 29, 37, 37, 37,
    48, 14, 48, 13, 32, 32,
    32, 21, 11, 21, 10, 6,
    13, 13, 10, 13, 17, 13,
    13, 17, 10, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28308166811516519, 52246410306956537, 33980592170803813, 29045132405682725, 28308166811516519, 29045132405682725,
    32989990871656069, 33166147806644091, 47213608532579404, 54396083269625807, 36747805441855883, 58491654791970033,
    41376851971437133, 36402669955592870, 55491655308588688, 35441144103407531, 35441144103407531, 40521891517292414,
    36322499606908879, 41376851971437133, 40521891517292414, 54396071635821383, 36402669955592870, 36322499606908879,
    36747805441855883, 55316032983079002, 34005234884518453, 32389575586574384, 56080991915990274, 35725398123250217,
    55316032912072042, 36727700909126590, 35569805596410828, 34005234884518453, 32389575586574384, 28221598169595408,
    33453206024373895, 34453096906169316, 29225692051789075, 37009633277236003, 37789029653343312, 37009633277236003,
    48885544380603783, 14120804863020662, 48885500750229896, 13134907566138845, 32036940623231739, 32816336999721460,
    32036940623231739, 21440222863012249, 11313449940963058, 21440222863012249, 10327552644081241, 6228818690495881,
    13497477645523802, 13134907566138845, 10327552644081241, 13560213400873323, 17121968510431347, 13291026768056127,
    13134907566138845, 17121968510431347, 10327552644081241, 13291026768056127
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
noncomputable def negativeCeiling : ℝ := 528257597369 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 784760300239460684829472849920, coefficient := (-784760300239460684829472849920) }, { argument := 6015011352687084124230226280448, coefficient := (-6015011352687084124230226280448) }, { argument := 1250711728506640466446972354560, coefficient := (-1250711728506640466446972354560) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 784760300239460684829472849920, coefficient := (-784760300239460684829472849920) }, { argument := 40872932304138577334868377600, coefficient := (-40872932304138577334868377600) }, { argument := 1258886314967468181913946030080, coefficient := (-1258886314967468181913946030080) }, { argument := 711189022092011245626709770240, coefficient := (-711189022092011245626709770240) }, { argument := 91871786037510943457293631488, coefficient := (-91871786037510943457293631488) }, { argument := 6672560230291013148870671597568, coefficient := (-6672560230291013148870671597568) }, { argument := 266085646679846568976615211008, coefficient := (-266085646679846568976615211008) }, { argument := 228145746315695978257709048791040, coefficient := (-228145746315695978257709048791040) }, { argument := 6584204406141735313187308306432, coefficient := (-6584204406141735313187308306432) }, { argument := 209471679301155809619888570368, coefficient := (-209471679301155809619888570368) }, { argument := 228145828013051500585053486841856, coefficient := (-228145828013051500585053486841856) }, { argument := 215133076039024885555561234432, coefficient := (-215133076039024885555561234432) }, { argument := 215133076039024885555561234432, coefficient := (-215133076039024885555561234432) }, { argument := 3640278102449815826637522993152, coefficient := (-3640278102449815826637522993152) }, { argument := 198148885825417657748543242240, coefficient := (-198148885825417657748543242240) }, { argument := 6584204406141735313187308306432, coefficient := (-6584204406141735313187308306432) }, { argument := 3640278102449815826637522993152, coefficient := (-3640278102449815826637522993152) }, { argument := 6672506423391054765135539208192, coefficient := (-6672506423391054765135539208192) }, { argument := 209471679301155809619888570368, coefficient := (-209471679301155809619888570368) }, { argument := 198148885825417657748543242240, coefficient := (-198148885825417657748543242240) }, { argument := 266085646679846568976615211008, coefficient := (-266085646679846568976615211008) }, { argument := 50499252801302770563654938001408, coefficient := (-50499252801302770563654938001408) }, { argument := 318064670825597822186479943680, coefficient := (-318064670825597822186479943680) }, { argument := 12973690520517805904974839808, coefficient := (-12973690520517805904974839808) }, { argument := 171628944712339018459299568418816, coefficient := (-171628944712339018459299568418816) }, { argument := 261984847285295048274653216768, coefficient := (-261984847285295048274653216768) }, { argument := 50499250315816779195687976828928, coefficient := (-50499250315816779195687976828928) }, { argument := 262403353431118203303845953536, coefficient := (-262403353431118203303845953536) }, { argument := 235200453952613126406318063616, coefficient := (-235200453952613126406318063616) }, { argument := 318064670825597822186479943680, coefficient := (-318064670825597822186479943680) }, { argument := 12973690520517805904974839808, coefficient := (-12973690520517805904974839808) }, { argument := 5773873931325013620191920128, coefficient := (-5773873931325013620191920128) }, { argument := 216939276261360431460878647296, coefficient := (-216939276261360431460878647296) }, { argument := 216922868684940234021081710592, coefficient := (-216922868684940234021081710592) }, { argument := 5790281507745211059988856832, coefficient := (-5790281507745211059988856832) }, { argument := 1276143379678109269400192286720, coefficient := (-1276143379678109269400192286720) }, { argument := 4380777087848439856705365344256, coefficient := (-4380777087848439856705365344256) }, { argument := 1276143379678109269400192286720, coefficient := (-1276143379678109269400192286720) }, { argument := 2341935805121168622221095075840, coefficient := (-2341935805121168622221095075840) }, { argument := 168257917784645458963988480, coefficient := (-168257917784645458963988480) }, { argument := 2341864980740007415394154315776, coefficient := (-2341864980740007415394154315776) }, { argument := 169910746053649834788782080, coefficient := (-169910746053649834788782080) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 139515193880523562315457495040, coefficient := (-139515193880523562315457495040) }, { argument := 40641508906946155076439244800, coefficient := (-40641508906946155076439244800) }, { argument := 107497872774792141000681717760, coefficient := (-107497872774792141000681717760) }, { argument := 192294763182451953101701120, coefficient := (-192294763182451953101701120) }, { argument := 107497872774792141000681717760, coefficient := (-107497872774792141000681717760) }, { argument := 194183709775599811187179520, coefficient := (-194183709775599811187179520) }, { argument := 1450710983537555009647411200, coefficient := (-1450710983537555009647411200) }, { argument := 218456673497549787585576960, coefficient := (-218456673497549787585576960) }, { argument := 169910746053649834788782080, coefficient := (-169910746053649834788782080) }, { argument := 194183709775599811187179520, coefficient := (-194183709775599811187179520) }, { argument := 228165858986329778144935936, coefficient := (-228165858986329778144935936) }, { argument := 2694298973136447380222115840, coefficient := (-2694298973136447380222115840) }, { argument := 6058531744998714109040001024, coefficient := (-6058531744998714109040001024) }, { argument := 169910746053649834788782080, coefficient := (-169910746053649834788782080) }, { argument := 2694298973136447380222115840, coefficient := (-2694298973136447380222115840) }, { argument := 194183709775599811187179520, coefficient := (-194183709775599811187179520) }, { argument := 189329117031209815907500032, coefficient := (-189329117031209815907500032) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
