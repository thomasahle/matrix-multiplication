import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 13, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13

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
def constantNumerator : ℤ := (-31020382022664484401461713128390656)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    100195, 11114589, 1039, 1347, 18043, 8129,
    1422655153, 18043, 1061, 133, 1039, 259,
    8129, 259, 12824911, 1347, 71316361164073, 6370685847075165,
    99623097443, 523667154197804073, 3884973645, 6534724907, 198029846871, 6452149547,
    3884973645, 3164199359421, 202668746515, 50965556058105767, 198029846871, 6534724907,
    202668746515, 6534724907, 198029846871, 6454508843, 71316361164073, 18478918449203251,
    204898221, 181203269587207091, 2312112069, 204870573, 181203295348732483, 204870573,
    204861357, 8491713957, 52676199, 2312112069, 8491713957, 18479058147975157,
    204861357, 52676199, 204898221, 13527, 61623, 1503,
    644787, 28557, 1503, 28557, 55611, 1050597,
    55611, 644787, 1050597, 13527
  ]
def negativeCoefficients : Array ℕ := #[
    60564161248143885079842652160, 6718356808252370832134171000832, 20097182825273595400315469824, 26054769264334487973267505152, 349002377012908067187576537088, 628950911209428515915936301056,
    6718299011208986990546400575488, 349002377012908067187576537088, 20522724713777944869812043776, 20580753153119447070197940224, 20097182825273595400315469824, 20039154385932093199929573376,
    628950911209428515915936301056, 20039154385932093199929573376, 60563929852186224467227181056, 26054769264334487973267505152, 80295084390984718786653847552, 14345509203491102879280707665920,
    229715222795156179390075764736, 147399200031962405833971899301888, 143330229124843090825854320640, 7534024871970278176804831232, 228312869011576827715409412096, 238042302837620036137495035904,
    143330229124843090825854320640, 3648073486339680701909770960896, 233661156168857474512338288640, 14345528704500953577815803953152, 228312869011576827715409412096, 7534024871970278176804831232,
    233661156168857474512338288640, 7534024871970278176804831232, 228312869011576827715409412096, 238129345496632289438073880576, 80295084390984718786653847552, 5201353140127596563783961542656,
    7559410087890759993652150272, 204016744347815346392084233846784, 85301879213156159783864107008, 7558390056730460150285991936, 204016773352714385368776957755392, 7558390056730460150285991936,
    7558050046343693535830605824, 313288948223852872443598209024, 7773634893830360073001500672, 85301879213156159783864107008, 313288948223852872443598209024, 5201392461836165312378665172992,
    7558050046343693535830605824, 7773634893830360073001500672, 7559410087890759993652150272, 255517805655110763222663168, 291006389773876147003588608, 227126938360098456197922816,
    3044920517390069928403402752, 269713239302616916735033344, 227126938360098456197922816, 269713239302616916735033344, 262615522478863839978848256, 9922608119606801305146753024,
    262615522478863839978848256, 3044920517390069928403402752, 9922608119606801305146753024, 255517805655110763222663168
  ]
def negativeScales : Array ℕ := #[
    16, 23, 10, 10, 14, 12,
    30, 14, 10, 7, 10, 8,
    12, 8, 23, 10, 46, 52,
    36, 58, 31, 32, 37, 32,
    31, 41, 37, 55, 37, 32,
    37, 32, 37, 32, 46, 54,
    27, 57, 31, 27, 57, 27,
    27, 32, 25, 31, 32, 54,
    27, 25, 27, 13, 15, 10,
    19, 14, 10, 14, 15, 20,
    15, 19, 20, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    16612450990411145, 23405951264971877, 10020979938904212, 10395534135462309, 14139151614223039, 12988862192585320,
    30405938853623550, 14139151614223039, 10051208940914765, 7055282435501190, 10020979938904212, 8016808287686554,
    12988862192585320, 8016808287686554, 23612445478332194, 10395534135462309, 46019298326508785, 52500370119954106,
    36535761216301223, 58861427733175881, 31855257667569159, 32605479358007361, 37526926932084899, 32587132731450740,
    31855257667569159, 41524977637886750, 37560332672161885, 55500372081124719, 37526926932084899, 32605479358007361,
    37560332672161885, 32605479358007361, 37526926932084899, 32587660171563375, 46019298326508785, 54036729838066878,
    27610332217513060, 57330386600338475, 31106564181527316, 27610137533910290, 57330386805445272, 27610137533910290,
    27610072633537494, 32983408647058794, 25650647911845638, 31106564181527316, 32983408647058794, 54036740744655604,
    27610072633537494, 25650647911845638, 27610332217513060, 13723554295483443, 15911181303864252, 10553629293917849,
    19298463131415911, 14801556808026795, 10553629293917849, 14801556808026795, 15763082659843835, 20002777939291802,
    15763082659843835, 19298463131415911, 20002777939291802, 13723554295483443
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
noncomputable def negativeCeiling : ℝ := 419325192907 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 60564161248143885079842652160, coefficient := (-60564161248143885079842652160) }, { argument := 6718356808252370832134171000832, coefficient := (-6718356808252370832134171000832) }, { argument := 20097182825273595400315469824, coefficient := (-20097182825273595400315469824) }, { argument := 26054769264334487973267505152, coefficient := (-26054769264334487973267505152) }, { argument := 349002377012908067187576537088, coefficient := (-349002377012908067187576537088) }, { argument := 628950911209428515915936301056, coefficient := (-628950911209428515915936301056) }, { argument := 6718299011208986990546400575488, coefficient := (-6718299011208986990546400575488) }, { argument := 349002377012908067187576537088, coefficient := (-349002377012908067187576537088) }, { argument := 20522724713777944869812043776, coefficient := (-20522724713777944869812043776) }, { argument := 20580753153119447070197940224, coefficient := (-20580753153119447070197940224) }, { argument := 20097182825273595400315469824, coefficient := (-20097182825273595400315469824) }, { argument := 20039154385932093199929573376, coefficient := (-20039154385932093199929573376) }, { argument := 628950911209428515915936301056, coefficient := (-628950911209428515915936301056) }, { argument := 20039154385932093199929573376, coefficient := (-20039154385932093199929573376) }, { argument := 60563929852186224467227181056, coefficient := (-60563929852186224467227181056) }, { argument := 26054769264334487973267505152, coefficient := (-26054769264334487973267505152) }, { argument := 80295084390984718786653847552, coefficient := (-80295084390984718786653847552) }, { argument := 14345509203491102879280707665920, coefficient := (-14345509203491102879280707665920) }, { argument := 229715222795156179390075764736, coefficient := (-229715222795156179390075764736) }, { argument := 147399200031962405833971899301888, coefficient := (-147399200031962405833971899301888) }, { argument := 143330229124843090825854320640, coefficient := (-143330229124843090825854320640) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 238042302837620036137495035904, coefficient := (-238042302837620036137495035904) }, { argument := 143330229124843090825854320640, coefficient := (-143330229124843090825854320640) }, { argument := 3648073486339680701909770960896, coefficient := (-3648073486339680701909770960896) }, { argument := 233661156168857474512338288640, coefficient := (-233661156168857474512338288640) }, { argument := 14345528704500953577815803953152, coefficient := (-14345528704500953577815803953152) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 233661156168857474512338288640, coefficient := (-233661156168857474512338288640) }, { argument := 7534024871970278176804831232, coefficient := (-7534024871970278176804831232) }, { argument := 228312869011576827715409412096, coefficient := (-228312869011576827715409412096) }, { argument := 238129345496632289438073880576, coefficient := (-238129345496632289438073880576) }, { argument := 80295084390984718786653847552, coefficient := (-80295084390984718786653847552) }, { argument := 5201353140127596563783961542656, coefficient := (-5201353140127596563783961542656) }, { argument := 7559410087890759993652150272, coefficient := (-7559410087890759993652150272) }, { argument := 204016744347815346392084233846784, coefficient := (-204016744347815346392084233846784) }, { argument := 85301879213156159783864107008, coefficient := (-85301879213156159783864107008) }, { argument := 7558390056730460150285991936, coefficient := (-7558390056730460150285991936) }, { argument := 204016773352714385368776957755392, coefficient := (-204016773352714385368776957755392) }, { argument := 7558390056730460150285991936, coefficient := (-7558390056730460150285991936) }, { argument := 7558050046343693535830605824, coefficient := (-7558050046343693535830605824) }, { argument := 313288948223852872443598209024, coefficient := (-313288948223852872443598209024) }, { argument := 7773634893830360073001500672, coefficient := (-7773634893830360073001500672) }, { argument := 85301879213156159783864107008, coefficient := (-85301879213156159783864107008) }, { argument := 313288948223852872443598209024, coefficient := (-313288948223852872443598209024) }, { argument := 5201392461836165312378665172992, coefficient := (-5201392461836165312378665172992) }, { argument := 7558050046343693535830605824, coefficient := (-7558050046343693535830605824) }, { argument := 7773634893830360073001500672, coefficient := (-7773634893830360073001500672) }, { argument := 7559410087890759993652150272, coefficient := (-7559410087890759993652150272) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 227126938360098456197922816, coefficient := (-227126938360098456197922816) }, { argument := 269713239302616916735033344, coefficient := (-269713239302616916735033344) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 3044920517390069928403402752, coefficient := (-3044920517390069928403402752) }, { argument := 9922608119606801305146753024, coefficient := (-9922608119606801305146753024) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }] }

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
def constantNumerator : ℤ := (-49273228569130406168931679856492544)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    55611, 55611, 61623, 2290886026958687, 13527, 351,
    33496885335852767, 21789, 9163326291123109, 21789, 22707, 13527,
    675, 351, 1599, 39, 16731, 741,
    39, 741, 1443, 27261, 1443, 16731,
    27261, 351, 1443, 1443, 1599, 48789789,
    61623, 1599, 5759426253, 99261, 1561398675, 99261,
    103443, 61623, 3075, 142267943743869, 142267952139907, 71316365396695,
    6370686219847331, 99623119773, 523667182920403927, 3884974515, 6534726357, 198029891241,
    6452150997, 3884974515, 3164200070211, 202668792045, 50965559040301145, 198029891241,
    6534726357, 202668792045, 6534726357, 198029891241, 6454510293, 71316365396695,
    67550678500985721, 24176012637, 331176805246946073, 272620273653
  ]
def negativeCoefficients : Array ℕ := #[
    262615522478863839978848256, 262615522478863839978848256, 291006389773876147003588608, 5158616728679709413526917349376, 255517805655110763222663168, 13260405083897963760058368,
    18857070039577344152188751970304, 411582573180986798244888576, 5158494108772037855129536299008, 411582573180986798244888576, 428923102906084135469580288, 255517805655110763222663168,
    12750389503748042076979200, 13260405083897963760058368, 15102128012217125393399808, 11787026741242634453385216, 158019827249784068140695552, 13997094255225628413394944,
    11787026741242634453385216, 13997094255225628413394944, 13628749669561796086726656, 514945730758037592682266624, 13628749669561796086726656, 158019827249784068140695552,
    514945730758037592682266624, 13260405083897963760058368, 13628749669561796086726656, 13628749669561796086726656, 15102128012217125393399808, 7200102008746315765033992192,
    291006389773876147003588608, 15102128012217125393399808, 26560665525123739668512243712, 468746819456123853556678656, 7200680438688549057016627200, 468746819456123853556678656,
    488495756087484709840355328, 291006389773876147003588608, 14521276934824159032115200, 80089732303956889502773936128, 80089737030506090526339497984, 80295089156493434286694727680,
    14345510042899396825127046873088, 229715274284630575131861712896, 147399208116655530808113325146112, 143330261222177779080474132480, 7534026543706459856732946432, 228312920166703987121209737216,
    238042356333177849895194722304, 143330261222177779080474132480, 3648074305824756961410533031936, 233661208661373579262081105920, 14345529543914328146991770501120, 228312920166703987121209737216,
    7534026543706459856732946432, 233661208661373579262081105920, 7534026543706459856732946432, 228312920166703987121209737216, 238129398992190103195773566976, 80295089156493434286694727680,
    19013825657853966775614204542976, 27873044864844186208501235712, 745743868351948829444343651631104, 314309776086347122774615523328
  ]
def negativeScales : Array ℕ := #[
    15, 15, 15, 51, 13, 8,
    54, 14, 53, 14, 14, 13,
    9, 8, 10, 5, 14, 9,
    5, 9, 10, 14, 10, 14,
    14, 8, 10, 10, 10, 25,
    15, 10, 32, 16, 30, 16,
    16, 15, 11, 47, 47, 46,
    52, 36, 58, 31, 32, 37,
    32, 31, 41, 37, 55, 37,
    32, 37, 32, 37, 32, 46,
    55, 34, 58, 37
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    15763082659843835, 15763082659843835, 15911181303864252, 51024827108739738, 13723554295483443, 8455327220304618,
    54894876476873017, 14411312365441260, 53024792815586256, 14411312365441260, 14470849492418713, 13723554295483443,
    9398743691938200, 8455327220304618, 10642954223498123, 5285402218862249, 14030236056361794, 9533329732306630,
    5285402218862249, 9533329732306630, 10494855584491427, 14734550864397523, 10494855584491427, 14030236056361794,
    14734550864397523, 8455327220304618, 10494855584491427, 10494855584491427, 10642954223498123, 25540075908302205,
    15911181303864252, 10642954223498123, 32423277953296301, 16598939368622512, 30540191804506134, 16598939368622512,
    16658476495620780, 15911181303864252, 11586370695117825, 47015603954365735, 47015604039507347, 46019298412132651,
    52500370204371475, 36535761539673789, 58861427812306207, 31855257990645892, 32605479678129112, 37526927255330979,
    32587133055669445, 31855257990645892, 41524977961966550, 37560332996266607, 55500372165542484, 37526927255330979,
    32605479678129112, 37560332996266607, 32605479678129112, 37526927255330979, 32587660495663570, 46019298412132651,
    55906819783652894, 34492857268597939, 58200379246891581, 37988101916774133
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
noncomputable def negativeCeiling : ℝ := 68034241797 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 262615522478863839978848256, coefficient := (-262615522478863839978848256) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 5158616728679709413526917349376, coefficient := (-5158616728679709413526917349376) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 18857070039577344152188751970304, coefficient := (-18857070039577344152188751970304) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 5158494108772037855129536299008, coefficient := (-5158494108772037855129536299008) }, { argument := 411582573180986798244888576, coefficient := (-411582573180986798244888576) }, { argument := 428923102906084135469580288, coefficient := (-428923102906084135469580288) }, { argument := 255517805655110763222663168, coefficient := (-255517805655110763222663168) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 15102128012217125393399808, coefficient := (-15102128012217125393399808) }, { argument := 11787026741242634453385216, coefficient := (-11787026741242634453385216) }, { argument := 158019827249784068140695552, coefficient := (-158019827249784068140695552) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 11787026741242634453385216, coefficient := (-11787026741242634453385216) }, { argument := 13997094255225628413394944, coefficient := (-13997094255225628413394944) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 514945730758037592682266624, coefficient := (-514945730758037592682266624) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 158019827249784068140695552, coefficient := (-158019827249784068140695552) }, { argument := 514945730758037592682266624, coefficient := (-514945730758037592682266624) }, { argument := 13260405083897963760058368, coefficient := (-13260405083897963760058368) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 13628749669561796086726656, coefficient := (-13628749669561796086726656) }, { argument := 15102128012217125393399808, coefficient := (-15102128012217125393399808) }, { argument := 7200102008746315765033992192, coefficient := (-7200102008746315765033992192) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 15102128012217125393399808, coefficient := (-15102128012217125393399808) }, { argument := 26560665525123739668512243712, coefficient := (-26560665525123739668512243712) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 7200680438688549057016627200, coefficient := (-7200680438688549057016627200) }, { argument := 468746819456123853556678656, coefficient := (-468746819456123853556678656) }, { argument := 488495756087484709840355328, coefficient := (-488495756087484709840355328) }, { argument := 291006389773876147003588608, coefficient := (-291006389773876147003588608) }, { argument := 14521276934824159032115200, coefficient := (-14521276934824159032115200) }, { argument := 80089732303956889502773936128, coefficient := (-80089732303956889502773936128) }, { argument := 80089737030506090526339497984, coefficient := (-80089737030506090526339497984) }, { argument := 80295089156493434286694727680, coefficient := (-80295089156493434286694727680) }, { argument := 14345510042899396825127046873088, coefficient := (-14345510042899396825127046873088) }, { argument := 229715274284630575131861712896, coefficient := (-229715274284630575131861712896) }, { argument := 147399208116655530808113325146112, coefficient := (-147399208116655530808113325146112) }, { argument := 143330261222177779080474132480, coefficient := (-143330261222177779080474132480) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 238042356333177849895194722304, coefficient := (-238042356333177849895194722304) }, { argument := 143330261222177779080474132480, coefficient := (-143330261222177779080474132480) }, { argument := 3648074305824756961410533031936, coefficient := (-3648074305824756961410533031936) }, { argument := 233661208661373579262081105920, coefficient := (-233661208661373579262081105920) }, { argument := 14345529543914328146991770501120, coefficient := (-14345529543914328146991770501120) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 233661208661373579262081105920, coefficient := (-233661208661373579262081105920) }, { argument := 7534026543706459856732946432, coefficient := (-7534026543706459856732946432) }, { argument := 228312920166703987121209737216, coefficient := (-228312920166703987121209737216) }, { argument := 238129398992190103195773566976, coefficient := (-238129398992190103195773566976) }, { argument := 80295089156493434286694727680, coefficient := (-80295089156493434286694727680) }, { argument := 19013825657853966775614204542976, coefficient := (-19013825657853966775614204542976) }, { argument := 27873044864844186208501235712, coefficient := (-27873044864844186208501235712) }, { argument := 745743868351948829444343651631104, coefficient := (-745743868351948829444343651631104) }, { argument := 314309776086347122774615523328, coefficient := (-314309776086347122774615523328) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk13
