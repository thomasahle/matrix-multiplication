import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 4, for level-four region 1, branch 1,
parent chunk 15, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard8

/-! Directed signed-log shard 8.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-757794305741883959947200684883968)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    7610563715, 7610565501, 2046397547, 175, 145, 7343711449,
    975, 511748015, 3905, 3905, 2795, 145,
    7607417987, 7607419773, 31, 1619799013, 16189816001, 32379624089,
    1619799013, 53890915415, 5355, 4437, 193429927165, 29835,
    13476642731, 119493, 119493, 85527, 4437, 14820571445,
    14820574923, 53891718231, 175, 145, 193444865277, 975,
    13476843435, 3905, 3905, 2795, 145, 459538378091,
    459538485909, 317, 14820571445, 14820574923, 633, 1192112027371,
    105, 87, 279187491391315, 585, 76291726523885, 2343,
    2343, 1677, 87, 126409731589751, 126409743415689, 260971,
    19620951809, 19620956415, 751, 31
  ]
def negativeCoefficients : Array ℕ := #[
    70195060553632599488824606720, 70195077026575057311454199808, 18874685911288006808726142976, 105781009216280052786790400, 5477945120128788447887360, 67733782825436867051537825792,
    147337834265532930667315200, 18880169325867753452056084480, 147526728924847716475863040, 147526728924847716475863040, 105592114556965266978242560, 5477945120128788447887360,
    70166046333961848388631658496, 70166062806904306211261251584, 4797017652230848565234106368, 3735002230457291369533669376, 149324696185447411089626103808, 149324659693175947273705619456,
    3735002230457291369533669376, 497055962279216985707716280320, 3236898882018169615275786240, 167625120675940926505353216, 1784076181304516980223844024320, 4508537728525307678419845120,
    497200358863150313982071406592, 4514317905100340124161409024, 4514317905100340124161409024, 3231118705443137169534222336, 167625120675940926505353216, 68347822118010688975960801280,
    68347838157454661066415931392, 497063366949862125311411355648, 3384992294920961689177292800, 175294243844121230332395520, 1784213961069021184992598818816, 4714810696497053781354086400,
    497207763533795453585766481920, 4720855325595126927227617280, 4720855325595126927227617280, 3378947665822888543303761920, 175294243844121230332395520, 2119246713173063375857872011264,
    2119247210395826510661981044736, 98106748113366386785755594752, 68347822118010688975960801280, 68347838157454661066415931392, 97952005608455714251393204224, 85900724516030754052957536256,
    126937211059536063344148480, 6573534144154546137464832, 314337170549107448462505410560, 176805401118639516800778240, 85896847786105068025272074240, 177032074709817259771035648,
    177032074709817259771035648, 126710537468358320373891072, 6573534144154546137464832, 142324705020901755134488346624, 142324718335724247661135527936, 9859205627207793448507670528,
    90485669125802864030133518336, 90485690367228664906682204160, 116211621187915073306155286528, 4797017652230848565234106368
  ]
def negativeScales : Array ℕ := #[
    32, 32, 30, 7, 7, 32,
    9, 28, 11, 11, 11, 7,
    32, 32, 4, 30, 33, 34,
    30, 35, 12, 12, 37, 14,
    33, 16, 16, 16, 12, 33,
    33, 35, 7, 7, 37, 9,
    33, 11, 11, 11, 7, 38,
    38, 8, 33, 33, 9, 40,
    6, 6, 47, 9, 46, 11,
    11, 10, 6, 46, 46, 17,
    34, 34, 9, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    32825356173271942, 32825356511834655, 30930439301435900, 7451211111832378, 7179909090014935, 32773862227482370,
    9929258415949272, 28930858367860654, 11931106840579056, 11931106840579056, 11448632567730597, 7179909090014935,
    32824759730664159, 32824760069366870, 4954196321574415, 30593167666522473, 33914367543861130, 34914367191292318,
    30593167666522473, 35649323042088436, 12386670859637623, 12115368837820224, 37493020067284943, 14864718158730226,
    33649742089436104, 16866566583203111, 16866566583203111, 16384092315535846, 12115368837820224, 33786882024876584,
    33786882363439293, 35649344533837587, 7451211111832378, 7179909090014935, 37493131478731408, 9929258415949272,
    33649763574943683, 11931106840579056, 11931106840579056, 11448632567730597, 7179909090014935, 38741394396363454,
    38741394734851997, 8308339030139408, 33786882024876584, 33786882363439293, 9306061689428342, 40116656956443606,
    6714245517766967, 6442943495848765, 47988227653066380, 9192292814470767, 46116591845639481, 11194141238863136,
    11194141238863136, 10711666973659367, 6442943495848765, 46845100862944222, 46845100997911852, 17993529994224486,
    34191675977016786, 34191676315688051, 9552669097515714, 4954196321574415
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
noncomputable def negativeCeiling : ℝ := 2677244549 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 70195060553632599488824606720, coefficient := (-70195060553632599488824606720) }, { argument := 70195077026575057311454199808, coefficient := (-70195077026575057311454199808) }, { argument := 18874685911288006808726142976, coefficient := (-18874685911288006808726142976) }, { argument := 105781009216280052786790400, coefficient := (-105781009216280052786790400) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 67733782825436867051537825792, coefficient := (-67733782825436867051537825792) }, { argument := 147337834265532930667315200, coefficient := (-147337834265532930667315200) }, { argument := 18880169325867753452056084480, coefficient := (-18880169325867753452056084480) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 147526728924847716475863040, coefficient := (-147526728924847716475863040) }, { argument := 105592114556965266978242560, coefficient := (-105592114556965266978242560) }, { argument := 5477945120128788447887360, coefficient := (-5477945120128788447887360) }, { argument := 70166046333961848388631658496, coefficient := (-70166046333961848388631658496) }, { argument := 70166062806904306211261251584, coefficient := (-70166062806904306211261251584) }, { argument := 4797017652230848565234106368, coefficient := (-4797017652230848565234106368) }, { argument := 3735002230457291369533669376, coefficient := (-3735002230457291369533669376) }, { argument := 149324696185447411089626103808, coefficient := (-149324696185447411089626103808) }, { argument := 149324659693175947273705619456, coefficient := (-149324659693175947273705619456) }, { argument := 3735002230457291369533669376, coefficient := (-3735002230457291369533669376) }, { argument := 497055962279216985707716280320, coefficient := (-497055962279216985707716280320) }, { argument := 3236898882018169615275786240, coefficient := (-3236898882018169615275786240) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 1784076181304516980223844024320, coefficient := (-1784076181304516980223844024320) }, { argument := 4508537728525307678419845120, coefficient := (-4508537728525307678419845120) }, { argument := 497200358863150313982071406592, coefficient := (-497200358863150313982071406592) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 4514317905100340124161409024, coefficient := (-4514317905100340124161409024) }, { argument := 3231118705443137169534222336, coefficient := (-3231118705443137169534222336) }, { argument := 167625120675940926505353216, coefficient := (-167625120675940926505353216) }, { argument := 68347822118010688975960801280, coefficient := (-68347822118010688975960801280) }, { argument := 68347838157454661066415931392, coefficient := (-68347838157454661066415931392) }, { argument := 497063366949862125311411355648, coefficient := (-497063366949862125311411355648) }, { argument := 3384992294920961689177292800, coefficient := (-3384992294920961689177292800) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 1784213961069021184992598818816, coefficient := (-1784213961069021184992598818816) }, { argument := 4714810696497053781354086400, coefficient := (-4714810696497053781354086400) }, { argument := 497207763533795453585766481920, coefficient := (-497207763533795453585766481920) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 4720855325595126927227617280, coefficient := (-4720855325595126927227617280) }, { argument := 3378947665822888543303761920, coefficient := (-3378947665822888543303761920) }, { argument := 175294243844121230332395520, coefficient := (-175294243844121230332395520) }, { argument := 2119246713173063375857872011264, coefficient := (-2119246713173063375857872011264) }, { argument := 2119247210395826510661981044736, coefficient := (-2119247210395826510661981044736) }, { argument := 98106748113366386785755594752, coefficient := (-98106748113366386785755594752) }, { argument := 68347822118010688975960801280, coefficient := (-68347822118010688975960801280) }, { argument := 68347838157454661066415931392, coefficient := (-68347838157454661066415931392) }, { argument := 97952005608455714251393204224, coefficient := (-97952005608455714251393204224) }, { argument := 85900724516030754052957536256, coefficient := (-85900724516030754052957536256) }, { argument := 126937211059536063344148480, coefficient := (-126937211059536063344148480) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 314337170549107448462505410560, coefficient := (-314337170549107448462505410560) }, { argument := 176805401118639516800778240, coefficient := (-176805401118639516800778240) }, { argument := 85896847786105068025272074240, coefficient := (-85896847786105068025272074240) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 177032074709817259771035648, coefficient := (-177032074709817259771035648) }, { argument := 126710537468358320373891072, coefficient := (-126710537468358320373891072) }, { argument := 6573534144154546137464832, coefficient := (-6573534144154546137464832) }, { argument := 142324705020901755134488346624, coefficient := (-142324705020901755134488346624) }, { argument := 142324718335724247661135527936, coefficient := (-142324718335724247661135527936) }, { argument := 9859205627207793448507670528, coefficient := (-9859205627207793448507670528) }, { argument := 90485669125802864030133518336, coefficient := (-90485669125802864030133518336) }, { argument := 90485690367228664906682204160, coefficient := (-90485690367228664906682204160) }, { argument := 116211621187915073306155286528, coefficient := (-116211621187915073306155286528) }, { argument := 4797017652230848565234106368, coefficient := (-4797017652230848565234106368) }] }

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

end TermShard8


end Parent3

namespace Parent3

namespace TermShard9

/-! Directed signed-log shard 9.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 423432850756697758629104851368280064
def positiveArguments : Array ℕ := #[
    13553, 3, 87, 77, 5, 3,
    5, 153, 5, 3, 2451, 157,
    87, 153, 5, 157, 5, 153,
    5, 3, 141, 105, 111, 9,
    1929, 3489, 105, 1929, 57, 57,
    111, 111, 3489, 111, 141, 9,
    31, 751, 569, 317, 31, 317,
    633, 31, 751, 31, 279, 837,
    1767, 4557, 3813, 106671, 3255, 3813,
    3441, 1767, 1767, 3441, 106671, 3441,
    279
  ]
def positiveCoefficients : Array ℕ := #[
    4295117146223298269621204635615232, 1856910058928070412348686336, 26925195854457020979055951872, 47660691512487140583616282624, 1547425049106725343623905280, 29710560942849126597578981376,
    1547425049106725343623905280, 47351206502665795514891501568, 49517601571415210995964968960, 29710560942849126597578981376, 758547759072116763444438368256, 48589146541951175789790625792,
    26925195854457020979055951872, 47351206502665795514891501568, 1547425049106725343623905280, 48589146541951175789790625792, 1547425049106725343623905280, 47351206502665795514891501568,
    49517601571415210995964968960, 1856910058928070412348686336, 5454673298101206836274266112, 4061990753905154027012751360, 4294104511271162828556337152, 5570730176784211237046059008,
    74624572993171829696262832128, 134974149908334118097595138048, 4061990753905154027012751360, 74624572993171829696262832128, 4410161389954167229328130048, 4410161389954167229328130048,
    4294104511271162828556337152, 4294104511271162828556337152, 134974149908334118097595138048, 4294104511271162828556337152, 5454673298101206836274266112, 5570730176784211237046059008,
    9594035304461697130468212736, 232423242375830146612310573056, 176096970588345344104400420864, 196213496226732773571511189504, 9594035304461697130468212736, 196213496226732773571511189504,
    195904011216911428502786408448, 9594035304461697130468212736, 232423242375830146612310573056, 9594035304461697130468212736, 345385270960621096696855658496, 259038953220465822522641743872,
    273430006177158368218344062976, 352580797438967369544706818048, 4720265369795154988190360666112, 8253268870663174956485280006144, 251843426742119549674790584320, 4720265369795154988190360666112,
    266234479698812095370492903424, 273430006177158368218344062976, 273430006177158368218344062976, 266234479698812095370492903424, 8253268870663174956485280006144, 266234479698812095370492903424,
    345385270960621096696855658496
  ]
def positiveScales : Array ℕ := #[
    13, 1, 6, 6, 2, 1,
    2, 7, 2, 1, 11, 7,
    6, 7, 2, 7, 2, 7,
    2, 1, 7, 6, 6, 3,
    10, 11, 6, 10, 5, 5,
    6, 6, 11, 6, 7, 3,
    4, 9, 9, 8, 4, 8,
    9, 4, 9, 4, 8, 9,
    10, 12, 11, 16, 11, 11,
    11, 10, 10, 11, 16, 11,
    8
  ]
def negativeArguments : Array ℕ := #[
    1, 3, 1
  ]
def negativeCoefficients : Array ℕ := #[
    1267650600228229401496703205376, 475368975085586025561263702016, 1267650600228229401496703205376
  ]
def negativeScales : Array ℕ := #[
    0, 1, 0
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13726324611642090, 1584962500720924, 6442943495848725, 6266786540694901, 2321928094887362, 1584962500720924,
    2321928094887362, 7257387842692651, 2321928094887362, 1584962500720924, 11259154768866839, 7294620748891626,
    6442943495848725, 7257387842692651, 2321928094887362, 7294620748891626, 2321928094887362, 7257387842692651,
    2321928094887362, 1584962500720924, 7139551352398793, 6714245517659862, 6794415866314396, 3169925001442312,
    10913637427705176, 11768597882173550, 6714245517659862, 10913637427705176, 5832890014087662, 5832890014087662,
    6794415866314396, 6794415866314396, 11768597882173550, 6794415866314396, 7139551352398793, 3169925001442312,
    4954196309696329, 9552669097514181, 9152284842306581, 8308339030139406, 4954196309696329, 8308339030139406,
    9306061689428341, 4954196309696329, 9552669097514181, 4954196309696329, 8124121311829187, 9709083812544787,
    10787086324520917, 12153868655223239, 11896710815471615, 16702808487119055, 11668441828050895, 11896710815471615,
    11748612176723449, 10787086324520917, 10787086324520917, 11748612176723449, 16702808487119055, 11748612176723449,
    8124121311829187
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 1584962500724866, 0
  ]

abbrev PositiveTerm := Fin 61
abbrev NegativeTerm := Fin 3
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
noncomputable def positiveFloor : ℝ := 715067815273 / 1000000000000
noncomputable def negativeCeiling : ℝ := 9069229 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 4295117146223298269621204635615232, coefficient := 4295117146223298269621204635615232 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 47660691512487140583616282624, coefficient := 47660691512487140583616282624 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 49517601571415210995964968960, coefficient := 49517601571415210995964968960 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 758547759072116763444438368256, coefficient := 758547759072116763444438368256 }, { argument := 48589146541951175789790625792, coefficient := 48589146541951175789790625792 }, { argument := 26925195854457020979055951872, coefficient := 26925195854457020979055951872 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 48589146541951175789790625792, coefficient := 48589146541951175789790625792 }, { argument := 1547425049106725343623905280, coefficient := 1547425049106725343623905280 }, { argument := 47351206502665795514891501568, coefficient := 47351206502665795514891501568 }, { argument := 49517601571415210995964968960, coefficient := 49517601571415210995964968960 }, { argument := 1856910058928070412348686336, coefficient := 1856910058928070412348686336 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 5570730176784211237046059008, coefficient := 5570730176784211237046059008 }, { argument := 475368975085586025561263702016, coefficient := (-475368975085586025561263702016) }, { argument := 9594035304461697130468212736, coefficient := 9594035304461697130468212736 }, { argument := 232423242375830146612310573056, coefficient := 232423242375830146612310573056 }, { argument := 176096970588345344104400420864, coefficient := 176096970588345344104400420864 }, { argument := 196213496226732773571511189504, coefficient := 196213496226732773571511189504 }, { argument := 9594035304461697130468212736, coefficient := 9594035304461697130468212736 }, { argument := 196213496226732773571511189504, coefficient := 196213496226732773571511189504 }, { argument := 195904011216911428502786408448, coefficient := 195904011216911428502786408448 }, { argument := 9594035304461697130468212736, coefficient := 9594035304461697130468212736 }, { argument := 232423242375830146612310573056, coefficient := 232423242375830146612310573056 }, { argument := 9594035304461697130468212736, coefficient := 9594035304461697130468212736 }, { argument := 1267650600228229401496703205376, coefficient := (-1267650600228229401496703205376) }, { argument := 345385270960621096696855658496, coefficient := 345385270960621096696855658496 }, { argument := 259038953220465822522641743872, coefficient := 259038953220465822522641743872 }, { argument := 273430006177158368218344062976, coefficient := 273430006177158368218344062976 }, { argument := 352580797438967369544706818048, coefficient := 352580797438967369544706818048 }, { argument := 4720265369795154988190360666112, coefficient := 4720265369795154988190360666112 }, { argument := 8253268870663174956485280006144, coefficient := 8253268870663174956485280006144 }, { argument := 251843426742119549674790584320, coefficient := 251843426742119549674790584320 }, { argument := 4720265369795154988190360666112, coefficient := 4720265369795154988190360666112 }, { argument := 266234479698812095370492903424, coefficient := 266234479698812095370492903424 }, { argument := 273430006177158368218344062976, coefficient := 273430006177158368218344062976 }, { argument := 273430006177158368218344062976, coefficient := 273430006177158368218344062976 }, { argument := 266234479698812095370492903424, coefficient := 266234479698812095370492903424 }, { argument := 8253268870663174956485280006144, coefficient := 8253268870663174956485280006144 }, { argument := 266234479698812095370492903424, coefficient := 266234479698812095370492903424 }, { argument := 345385270960621096696855658496, coefficient := 345385270960621096696855658496 }] }

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

end TermShard9


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk15
