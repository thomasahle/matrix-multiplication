import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 2,
parent chunk 16, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2734960730846759859043737828065280)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    427419603, 35941390381, 17970690855, 213714137, 1886451, 301166607,
    12020759373, 301166607, 7544943, 1102142187, 92678300949, 46339139295,
    551082273, 706161491, 112736699887, 4499770925293, 112736699887, 2824323663,
    452634135, 16715176425, 133721378655, 3621105825, 28296765, 4517499105,
    180311390595, 4517499105, 113174145, 31806723, 1174579965, 9396637419,
    254456085, 7811913641, 27946605267, 1952977761, 306522477, 2143902179,
    31516725, 296257215, 3498356475, 245830455, 2143901715, 3498356475,
    31516725, 245830455, 245830455, 245830455, 245830455, 245830455,
    306522941, 296257215, 551267103, 1050410361, 9071725845, 84743451381,
    299067885, 697825065, 9071725845, 9071725845, 299067885, 111951078285,
    4486018275, 1050410361, 9071725845, 697825065
  ]
def negativeCoefficients : Array ℕ := #[
    1971125007156884822254682112, 165750407502898308359781351424, 165750367514968842575900835840, 1971164995086350606135197696, 556782060873495317688877056, 88888693166023417018913390592,
    886975486901505181870637187072, 88888693166023417018913390592, 556718530286905461993111552, 10165467428213767210423812096, 854806449396218031741748641792, 854806243170842659705816350720,
    10165673653589139246356103168, 13026380299186150870096019456, 2079625050530089527338327867392, 20751530662299798317515115855872, 2079625050530089527338327867392, 13024893948170725704547172352,
    33398504189479596547784048640, 1233362326635513437876335411200, 1233362024616196091066701578240, 33398806208796943357417881600, 1043966364137803720666644480, 166666299686293906910462607360,
    1663079037940322216007444725760, 166666299686293906910462607360, 1043847244287947741237084160, 75101501312559525210152239104, 2773398529083100487332732600320, 2773397849947770669641880305664,
    75102180447889342901004533760, 18013046457680944467627999232, 64440484386166548927489245184, 18013040469406649539664805888, 2827170843029261169947836416, 19774007407540622161327685632,
    2325523840465934672619110400, 2732490512547473240327454720, 32266643286464843582590156800, 72556343822537161785716244480, 19774003127895997060711710720, 32266643286464843582590156800,
    2325523840465934672619110400, 2267385744454286305803632640, 2267385744454286305803632640, 2267385744454286305803632640, 72556343822537161785716244480, 2267385744454286305803632640,
    2827175122673886270563811328, 2732490512547473240327454720, 5084541582648141491390644224, 155013208813918885776885547008, 167343804969571524418228715520, 781620379774077633842902990848,
    88269259764169595297527234560, 6436300191137366323778027520, 167343804969571524418228715520, 167343804969571524418228715520, 88269259764169595297527234560, 2065132889899217823315064258560,
    165504862057817991182863564800, 155013208813918885776885547008, 167343804969571524418228715520, 6436300191137366323778027520
  ]
def negativeScales : Array ℕ := #[
    28, 35, 34, 27, 20, 28,
    33, 28, 22, 30, 36, 35,
    29, 29, 36, 42, 36, 31,
    28, 33, 36, 31, 24, 32,
    37, 32, 26, 24, 30, 33,
    27, 32, 34, 30, 28, 30,
    24, 28, 31, 27, 30, 31,
    24, 27, 27, 27, 27, 27,
    28, 28, 29, 29, 33, 36,
    28, 29, 33, 33, 28, 36,
    32, 29, 33, 29
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28671077835832628, 35064927168989549, 34064926820933726, 27671107103282540, 20847243198030246, 28165986573643116,
    33484808985443419, 28165986573643116, 22847078572585184, 30037663211513457, 36431512544706501, 35431512196650678,
    29037692478963342, 29395422908066517, 36714166285423221, 42032988697122702, 36714166285423221, 31395258282626630,
    28753770147611648, 33960439543657442, 36960439190377707, 31753783193699016, 24754133792241662, 32072877169251634,
    37391699581051780, 32072877169251634, 26753969166800896, 24922828411531762, 30129497788861997, 33129497435582336,
    27922841457620549, 32863028856836993, 34701953995455768, 30863028377225982, 28191417628341115, 30997591957429546,
    24909614297091590, 28142275048697877, 31704030158337271, 27873088418556653, 30997591645190106, 31704030158337271,
    24909614297091590, 27873088418556653, 27873088418556653, 27873088418556653, 27873088418556653, 27873088418556653,
    28191419812226613, 28142275048697877, 29038176269915125, 29968305919956791, 33078729895497072, 36302382835999486,
    28155897756019532, 29378290177355982, 33078729895497072, 33078729895497072, 28155897756019532, 36704077467778628,
    32062788351628050, 29968305919956791, 33078729895497072, 29378290177355982
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
noncomputable def negativeCeiling : ℝ := 19664949217 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1971125007156884822254682112, coefficient := (-1971125007156884822254682112) }, { argument := 165750407502898308359781351424, coefficient := (-165750407502898308359781351424) }, { argument := 165750367514968842575900835840, coefficient := (-165750367514968842575900835840) }, { argument := 1971164995086350606135197696, coefficient := (-1971164995086350606135197696) }, { argument := 556782060873495317688877056, coefficient := (-556782060873495317688877056) }, { argument := 88888693166023417018913390592, coefficient := (-88888693166023417018913390592) }, { argument := 886975486901505181870637187072, coefficient := (-886975486901505181870637187072) }, { argument := 88888693166023417018913390592, coefficient := (-88888693166023417018913390592) }, { argument := 556718530286905461993111552, coefficient := (-556718530286905461993111552) }, { argument := 10165467428213767210423812096, coefficient := (-10165467428213767210423812096) }, { argument := 854806449396218031741748641792, coefficient := (-854806449396218031741748641792) }, { argument := 854806243170842659705816350720, coefficient := (-854806243170842659705816350720) }, { argument := 10165673653589139246356103168, coefficient := (-10165673653589139246356103168) }, { argument := 13026380299186150870096019456, coefficient := (-13026380299186150870096019456) }, { argument := 2079625050530089527338327867392, coefficient := (-2079625050530089527338327867392) }, { argument := 20751530662299798317515115855872, coefficient := (-20751530662299798317515115855872) }, { argument := 2079625050530089527338327867392, coefficient := (-2079625050530089527338327867392) }, { argument := 13024893948170725704547172352, coefficient := (-13024893948170725704547172352) }, { argument := 33398504189479596547784048640, coefficient := (-33398504189479596547784048640) }, { argument := 1233362326635513437876335411200, coefficient := (-1233362326635513437876335411200) }, { argument := 1233362024616196091066701578240, coefficient := (-1233362024616196091066701578240) }, { argument := 33398806208796943357417881600, coefficient := (-33398806208796943357417881600) }, { argument := 1043966364137803720666644480, coefficient := (-1043966364137803720666644480) }, { argument := 166666299686293906910462607360, coefficient := (-166666299686293906910462607360) }, { argument := 1663079037940322216007444725760, coefficient := (-1663079037940322216007444725760) }, { argument := 166666299686293906910462607360, coefficient := (-166666299686293906910462607360) }, { argument := 1043847244287947741237084160, coefficient := (-1043847244287947741237084160) }, { argument := 75101501312559525210152239104, coefficient := (-75101501312559525210152239104) }, { argument := 2773398529083100487332732600320, coefficient := (-2773398529083100487332732600320) }, { argument := 2773397849947770669641880305664, coefficient := (-2773397849947770669641880305664) }, { argument := 75102180447889342901004533760, coefficient := (-75102180447889342901004533760) }, { argument := 18013046457680944467627999232, coefficient := (-18013046457680944467627999232) }, { argument := 64440484386166548927489245184, coefficient := (-64440484386166548927489245184) }, { argument := 18013040469406649539664805888, coefficient := (-18013040469406649539664805888) }, { argument := 2827170843029261169947836416, coefficient := (-2827170843029261169947836416) }, { argument := 19774007407540622161327685632, coefficient := (-19774007407540622161327685632) }, { argument := 2325523840465934672619110400, coefficient := (-2325523840465934672619110400) }, { argument := 2732490512547473240327454720, coefficient := (-2732490512547473240327454720) }, { argument := 32266643286464843582590156800, coefficient := (-32266643286464843582590156800) }, { argument := 72556343822537161785716244480, coefficient := (-72556343822537161785716244480) }, { argument := 19774003127895997060711710720, coefficient := (-19774003127895997060711710720) }, { argument := 32266643286464843582590156800, coefficient := (-32266643286464843582590156800) }, { argument := 2325523840465934672619110400, coefficient := (-2325523840465934672619110400) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 72556343822537161785716244480, coefficient := (-72556343822537161785716244480) }, { argument := 2267385744454286305803632640, coefficient := (-2267385744454286305803632640) }, { argument := 2827175122673886270563811328, coefficient := (-2827175122673886270563811328) }, { argument := 2732490512547473240327454720, coefficient := (-2732490512547473240327454720) }, { argument := 5084541582648141491390644224, coefficient := (-5084541582648141491390644224) }, { argument := 155013208813918885776885547008, coefficient := (-155013208813918885776885547008) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 781620379774077633842902990848, coefficient := (-781620379774077633842902990848) }, { argument := 88269259764169595297527234560, coefficient := (-88269259764169595297527234560) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 88269259764169595297527234560, coefficient := (-88269259764169595297527234560) }, { argument := 2065132889899217823315064258560, coefficient := (-2065132889899217823315064258560) }, { argument := 165504862057817991182863564800, coefficient := (-165504862057817991182863564800) }, { argument := 155013208813918885776885547008, coefficient := (-155013208813918885776885547008) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }] }

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


end Parent3

namespace Parent3

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-509068201841955570988774609387520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    4486018275, 697825065, 9071725845, 9071725845, 650950371, 264810065,
    2244522915, 20291614365, 35321702715, 1063195065, 20291610235, 1063195065,
    1063195065, 91080377235, 1063195065, 35321702715, 91080377235, 2118482585,
    1063195065, 1063195065, 2244522915, 57222347, 9135387079, 364629700981,
    9135387079, 228863271, 452634135, 16715176425, 133721378655, 3621105825,
    12103462845, 1856437383, 104294235, 48412217785, 5638841639, 756466185,
    5638841639, 5638841639, 1856437383, 104294235, 4077785, 150587175,
    1204697105, 32622575, 3390075731, 12127772097, 847518651, 21534885,
    104294235, 21534885, 12865473, 1081847871, 540923805, 6432867,
    4401719, 702722083, 28048438537, 702722083, 17604867, 12865473,
    1081847871, 540923805, 6432867, 28296765
  ]
def negativeCoefficients : Array ℕ := #[
    165504862057817991182863564800, 6436300191137366323778027520, 167343804969571524418228715520, 167343804969571524418228715520, 6003957449261641985339424768, 19539533988789564618215260160,
    20702069890290768828243640320, 93578554258390839102233640960, 162892602557814207359074959360, 19612487264485991521493975040, 93578535212127582997121597440, 19612487264485991521493975040,
    19612487264485991521493975040, 840068204495483303503991930880, 19612487264485991521493975040, 162892602557814207359074959360, 840068204495483303503991930880, 19539553035052820723327303680,
    19612487264485991521493975040, 19612487264485991521493975040, 20702069890290768828243640320, 1055565990406001539785162752, 168518147460586061431689969664, 1681557693917436907296416333824,
    168518147460586061431689969664, 1055445547002258271695273984, 33398504189479596547784048640, 1233362326635513437876335411200, 1233362024616196091066701578240, 33398806208796943357417881600,
    13954342594210468706616606720, 8561306323267029776027615232, 480972265352080324495933440, 55815486970036556604280668160, 13002283573351238105540067328, 13954338115110423309016104960,
    13002283573351238105540067328, 13002283573351238105540067328, 8561306323267029776027615232, 480972265352080324495933440, 2407099401043574525966417920, 88890978496253220747843993600,
    88890956729095213770573086720, 2407121168201581503237324800, 15633964850062706519073357824, 55929477014408702842726514688, 15633959652692563751407190016, 49656064031470839681515520,
    480972265352080324495933440, 49656064031470839681515520, 237326087818220246157754368, 19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144,
    40598691938692366914813952, 6481467210022540824295768064, 64675295919901419511400628224, 6481467210022540824295768064, 40594059500086856603664384, 237326087818220246157754368,
    19956570803024545488134209536, 19956565988424342249941237760, 237330902418423484350726144, 1043966364137803720666644480
  ]
def negativeScales : Array ℕ := #[
    32, 29, 33, 33, 29, 27,
    31, 34, 35, 29, 34, 29,
    29, 36, 29, 35, 36, 30,
    29, 29, 31, 25, 33, 38,
    33, 27, 28, 33, 36, 31,
    33, 30, 26, 35, 32, 29,
    32, 32, 30, 26, 21, 27,
    30, 24, 31, 33, 29, 24,
    26, 24, 23, 30, 29, 22,
    22, 29, 34, 29, 24, 23,
    30, 29, 22, 24
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32062788351628050, 29378290177355982, 33078729895497072, 33078729895497072, 29277972314407601, 27980382734035665,
    31063761679216376, 34240164596803594, 35039835839970895, 29985759186047660, 34240164303168449, 29985759186047660,
    29985759186047660, 36406421215687833, 29985759186047660, 35039835839970895, 36406421215687833, 30980384140309934,
    29985759186047660, 29985759186047660, 31063761679216376, 25770075336211188, 33088818713120656, 38407641124920806,
    33088818713120656, 27769910710770090, 28753770147611648, 33960439543657442, 36960439190377707, 31753783193699016,
    33494700815760347, 30789889508912656, 26636084172323563, 35494652135081148, 32392751680917429, 29494700352680383,
    32392751680917429, 32392751680917429, 30789889508912656, 26636084172323563, 21959354293214660, 27166023664887111,
    30166023311607450, 24959367339304617, 31658670356140714, 33497595496874045, 29658669876529723, 24360172283571542,
    26636084172323563, 24360172283571542, 23617001163049725, 30010850496233756, 29010850148177933, 22617030430499618,
    22069635617723515, 29388378994979568, 34707201406865376, 29388378994979568, 24069470992283627, 23617001163049725,
    30010850496233756, 29010850148177933, 22617030430499618, 24754133792241662
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
noncomputable def negativeCeiling : ℝ := 3427556303 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 165504862057817991182863564800, coefficient := (-165504862057817991182863564800) }, { argument := 6436300191137366323778027520, coefficient := (-6436300191137366323778027520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 167343804969571524418228715520, coefficient := (-167343804969571524418228715520) }, { argument := 6003957449261641985339424768, coefficient := (-6003957449261641985339424768) }, { argument := 19539533988789564618215260160, coefficient := (-19539533988789564618215260160) }, { argument := 20702069890290768828243640320, coefficient := (-20702069890290768828243640320) }, { argument := 93578554258390839102233640960, coefficient := (-93578554258390839102233640960) }, { argument := 162892602557814207359074959360, coefficient := (-162892602557814207359074959360) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 93578535212127582997121597440, coefficient := (-93578535212127582997121597440) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 840068204495483303503991930880, coefficient := (-840068204495483303503991930880) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 162892602557814207359074959360, coefficient := (-162892602557814207359074959360) }, { argument := 840068204495483303503991930880, coefficient := (-840068204495483303503991930880) }, { argument := 19539553035052820723327303680, coefficient := (-19539553035052820723327303680) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 19612487264485991521493975040, coefficient := (-19612487264485991521493975040) }, { argument := 20702069890290768828243640320, coefficient := (-20702069890290768828243640320) }, { argument := 1055565990406001539785162752, coefficient := (-1055565990406001539785162752) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1681557693917436907296416333824, coefficient := (-1681557693917436907296416333824) }, { argument := 168518147460586061431689969664, coefficient := (-168518147460586061431689969664) }, { argument := 1055445547002258271695273984, coefficient := (-1055445547002258271695273984) }, { argument := 33398504189479596547784048640, coefficient := (-33398504189479596547784048640) }, { argument := 1233362326635513437876335411200, coefficient := (-1233362326635513437876335411200) }, { argument := 1233362024616196091066701578240, coefficient := (-1233362024616196091066701578240) }, { argument := 33398806208796943357417881600, coefficient := (-33398806208796943357417881600) }, { argument := 13954342594210468706616606720, coefficient := (-13954342594210468706616606720) }, { argument := 8561306323267029776027615232, coefficient := (-8561306323267029776027615232) }, { argument := 480972265352080324495933440, coefficient := (-480972265352080324495933440) }, { argument := 55815486970036556604280668160, coefficient := (-55815486970036556604280668160) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 13954338115110423309016104960, coefficient := (-13954338115110423309016104960) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 13002283573351238105540067328, coefficient := (-13002283573351238105540067328) }, { argument := 8561306323267029776027615232, coefficient := (-8561306323267029776027615232) }, { argument := 480972265352080324495933440, coefficient := (-480972265352080324495933440) }, { argument := 2407099401043574525966417920, coefficient := (-2407099401043574525966417920) }, { argument := 88890978496253220747843993600, coefficient := (-88890978496253220747843993600) }, { argument := 88890956729095213770573086720, coefficient := (-88890956729095213770573086720) }, { argument := 2407121168201581503237324800, coefficient := (-2407121168201581503237324800) }, { argument := 15633964850062706519073357824, coefficient := (-15633964850062706519073357824) }, { argument := 55929477014408702842726514688, coefficient := (-55929477014408702842726514688) }, { argument := 15633959652692563751407190016, coefficient := (-15633959652692563751407190016) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 480972265352080324495933440, coefficient := (-480972265352080324495933440) }, { argument := 49656064031470839681515520, coefficient := (-49656064031470839681515520) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 40598691938692366914813952, coefficient := (-40598691938692366914813952) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 64675295919901419511400628224, coefficient := (-64675295919901419511400628224) }, { argument := 6481467210022540824295768064, coefficient := (-6481467210022540824295768064) }, { argument := 40594059500086856603664384, coefficient := (-40594059500086856603664384) }, { argument := 237326087818220246157754368, coefficient := (-237326087818220246157754368) }, { argument := 19956570803024545488134209536, coefficient := (-19956570803024545488134209536) }, { argument := 19956565988424342249941237760, coefficient := (-19956565988424342249941237760) }, { argument := 237330902418423484350726144, coefficient := (-237330902418423484350726144) }, { argument := 1043966364137803720666644480, coefficient := (-1043966364137803720666644480) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk16
