import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 15, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15

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
def constantNumerator : ℤ := (-1983141958052779640728093391323136)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    16846524229, 43065026337, 194535826057, 19078844667, 3615490885, 76202132433,
    37708898833, 16850718533, 43065026337, 3611296581, 151343642701899, 6438604118953909,
    511570675, 4808531065, 56806587165, 3989749425, 1609650763382383, 56806587165,
    511570675, 3990271425, 3990156225, 3990271425, 3989749425, 3990156225,
    37836177031569, 4808531065, 28035, 7209, 28035, 24831,
    1162251, 316395, 7209, 1162251, 28035, 28035,
    12015, 28035, 316395, 12015, 28035, 24831,
    1691136016407, 196866453736733, 504770539, 7701967340003347, 16640787, 38828503,
    504770539, 504770539, 16640787, 6229201267, 249611805, 196866456825117,
    504770539, 38828503, 249611805, 38828503, 504770539, 504770539,
    7127753406121, 1575, 405, 1575
  ]
def negativeCoefficients : Array ℕ := #[
    38845440122988765400958763008, 198602379841550127407875227648, 448569074555144614988704907264, 175971282397103666877941415936, 8336754382053081500635627520, 175710154357809145727435145216,
    173901601518438944228383916032, 38855111529545682434356412416, 198602379841550127407875227648, 8327082975496164467237978112, 170397793219291455709538942976, 7249223777726741318561972617216,
    75494506538718760593155686400, 88701741926537028732756951040, 1047896575133628828767370608640, 2355132369958554917662202265600, 7249222578165534506401260371968, 1047896575133628828767370608640,
    75494506538718760593155686400, 73607515761611317562887372800, 73605390696694026222541209600, 73607515761611317562887372800, 2355132369958554917662202265600, 73605390696694026222541209600,
    170398992780498267870251188224, 88701741926537028732756951040, 264783088694501007131934720, 272348319800058178764275712, 264783088694501007131934720, 234522164272272320602570752,
    10977150334163456038526779392, 2988266286695082794774691840, 272348319800058178764275712, 10977150334163456038526779392, 264783088694501007131934720, 264783088694501007131934720,
    226956933166715148970229760, 264783088694501007131934720, 2988266286695082794774691840, 226956933166715148970229760, 264783088694501007131934720, 234522164272272320602570752,
    7616199533323390209723727872, 886607687690501728642235629568, 74490983591051408789253128192, 8671644310614700954888362262528, 39291947388686457383342309376, 2865037830425054184202043392,
    74490983591051408789253128192, 74490983591051408789253128192, 39291947388686457383342309376, 919267852447810242531112779776, 73672401353787107593766830080, 886607701599346760219237548032,
    74490983591051408789253128192, 2865037830425054184202043392, 73672401353787107593766830080, 2865037830425054184202043392, 74490983591051408789253128192, 74490983591051408789253128192,
    8025136895948829810705301504, 14875454421039382423142400, 15300467404497650492375040, 14875454421039382423142400
  ]
def negativeScales : Array ℕ := #[
    33, 35, 37, 34, 31, 36,
    35, 33, 35, 31, 47, 52,
    28, 32, 35, 31, 50, 35,
    28, 31, 31, 31, 31, 31,
    45, 32, 14, 12, 14, 14,
    20, 18, 12, 20, 14, 14,
    13, 14, 18, 13, 14, 14,
    40, 47, 28, 52, 23, 25,
    28, 28, 23, 32, 27, 47,
    28, 25, 27, 25, 28, 28,
    42, 10, 8, 10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33971731929450465, 35325797662439833, 37501244912675448, 34151254759438454, 31751544393311161, 36149112319393641,
    35134185970703889, 33972091074746180, 35325797662439833, 31749869761998466, 47104821403422846, 52515669371131366,
    28930358332873119, 32162949093324014, 35725339180129077, 31893650999151501, 50515669132402200, 35725339180129077,
    28930358332873119, 31893839742233674, 31893798090711289, 31893839742233674, 31893650999151501, 31893798090711289,
    45104831559627806, 32162949093324014, 14774941449737867, 12815583434735727, 14774941449737867, 14599854742801218,
    20148490236475455, 18271367275473176, 12815583434735727, 20148490236475455, 14774941449737867, 14774941449737867,
    13552549028018665, 14774941449737867, 18271367275473176, 13552549028018665, 14774941449737867, 14599854742801218,
    40621129837616426, 47484210623761859, 28911052474105241, 52774148429124482, 23988220348907675, 25210612750646476,
    28911052474105241, 28911052474105241, 23988220348907675, 32536400040990349, 27895110928918576, 47484210646394442,
    28911052474105241, 25210612750646476, 27895110928918576, 25210612750646476, 28911052474105241, 28911052474105241,
    42696584564531161, 10621136113284685, 8661778097800657, 10621136113284685
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
noncomputable def negativeCeiling : ℝ := 19882783357 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 38845440122988765400958763008, coefficient := (-38845440122988765400958763008) }, { argument := 198602379841550127407875227648, coefficient := (-198602379841550127407875227648) }, { argument := 448569074555144614988704907264, coefficient := (-448569074555144614988704907264) }, { argument := 175971282397103666877941415936, coefficient := (-175971282397103666877941415936) }, { argument := 8336754382053081500635627520, coefficient := (-8336754382053081500635627520) }, { argument := 175710154357809145727435145216, coefficient := (-175710154357809145727435145216) }, { argument := 173901601518438944228383916032, coefficient := (-173901601518438944228383916032) }, { argument := 38855111529545682434356412416, coefficient := (-38855111529545682434356412416) }, { argument := 198602379841550127407875227648, coefficient := (-198602379841550127407875227648) }, { argument := 8327082975496164467237978112, coefficient := (-8327082975496164467237978112) }, { argument := 170397793219291455709538942976, coefficient := (-170397793219291455709538942976) }, { argument := 7249223777726741318561972617216, coefficient := (-7249223777726741318561972617216) }, { argument := 75494506538718760593155686400, coefficient := (-75494506538718760593155686400) }, { argument := 88701741926537028732756951040, coefficient := (-88701741926537028732756951040) }, { argument := 1047896575133628828767370608640, coefficient := (-1047896575133628828767370608640) }, { argument := 2355132369958554917662202265600, coefficient := (-2355132369958554917662202265600) }, { argument := 7249222578165534506401260371968, coefficient := (-7249222578165534506401260371968) }, { argument := 1047896575133628828767370608640, coefficient := (-1047896575133628828767370608640) }, { argument := 75494506538718760593155686400, coefficient := (-75494506538718760593155686400) }, { argument := 73607515761611317562887372800, coefficient := (-73607515761611317562887372800) }, { argument := 73605390696694026222541209600, coefficient := (-73605390696694026222541209600) }, { argument := 73607515761611317562887372800, coefficient := (-73607515761611317562887372800) }, { argument := 2355132369958554917662202265600, coefficient := (-2355132369958554917662202265600) }, { argument := 73605390696694026222541209600, coefficient := (-73605390696694026222541209600) }, { argument := 170398992780498267870251188224, coefficient := (-170398992780498267870251188224) }, { argument := 88701741926537028732756951040, coefficient := (-88701741926537028732756951040) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 272348319800058178764275712, coefficient := (-272348319800058178764275712) }, { argument := 10977150334163456038526779392, coefficient := (-10977150334163456038526779392) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 2988266286695082794774691840, coefficient := (-2988266286695082794774691840) }, { argument := 226956933166715148970229760, coefficient := (-226956933166715148970229760) }, { argument := 264783088694501007131934720, coefficient := (-264783088694501007131934720) }, { argument := 234522164272272320602570752, coefficient := (-234522164272272320602570752) }, { argument := 7616199533323390209723727872, coefficient := (-7616199533323390209723727872) }, { argument := 886607687690501728642235629568, coefficient := (-886607687690501728642235629568) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 8671644310614700954888362262528, coefficient := (-8671644310614700954888362262528) }, { argument := 39291947388686457383342309376, coefficient := (-39291947388686457383342309376) }, { argument := 2865037830425054184202043392, coefficient := (-2865037830425054184202043392) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 39291947388686457383342309376, coefficient := (-39291947388686457383342309376) }, { argument := 919267852447810242531112779776, coefficient := (-919267852447810242531112779776) }, { argument := 73672401353787107593766830080, coefficient := (-73672401353787107593766830080) }, { argument := 886607701599346760219237548032, coefficient := (-886607701599346760219237548032) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 2865037830425054184202043392, coefficient := (-2865037830425054184202043392) }, { argument := 73672401353787107593766830080, coefficient := (-73672401353787107593766830080) }, { argument := 2865037830425054184202043392, coefficient := (-2865037830425054184202043392) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 74490983591051408789253128192, coefficient := (-74490983591051408789253128192) }, { argument := 8025136895948829810705301504, coefficient := (-8025136895948829810705301504) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }] }

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
def constantNumerator : ℤ := (-22238260158229549945759844720967680)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1395, 65295, 17775, 405, 65295, 1575,
    1575, 675, 1575, 17775, 675, 1575,
    1395, 89558989, 9390098471, 101215876125, 4695052817, 89558989,
    1696075342975, 45848501, 61336365502849, 721510621, 21717711, 122668828267493,
    21717711, 21717711, 1860483909, 21717711, 721510621, 1860483909,
    3396053424155, 21717711, 21717711, 45848501, 16846522555, 43065006303,
    194535796087, 19078835973, 3615489211, 76202097711, 37708881391, 16850716859,
    43065006303, 3611294907, 1069309579193175, 46719621468820649, 878691325, 8257851655,
    97710821475, 6849819435, 23359806842238629, 97710821475, 878691325, 6853951935,
    6853039935, 6853951935, 6849819435, 6853039935, 534658681768283, 8257851655,
    61190913008361, 7189686708984803, 18293051413, 280958388530244589
  ]
def negativeCoefficients : Array ℕ := #[
    13175402487206310146211840, 616693838997946968456560640, 167880128466015887346892800, 15300467404497650492375040, 616693838997946968456560640, 14875454421039382423142400,
    14875454421039382423142400, 12750389503748042076979200, 14875454421039382423142400, 167880128466015887346892800, 12750389503748042076979200, 14875454421039382423142400,
    13175402487206310146211840, 206508968697896115296534528, 21652092915183546490937147392, 233387920384270480699293696000, 21652109431937021488626925568, 206508968697896115296534528,
    7638444282614496200595865600, 211438891027554112743931904, 276234432822891301910666543104, 1663690221506281045011464192, 200310528341893369967935488, 276225644637728420611452043264,
    200310528341893369967935488, 200310528341893369967935488, 8579967630644432680293236736, 200310528341893369967935488, 1663690221506281045011464192, 8579967630644432680293236736,
    7647232467777377499810365440, 200310528341893369967935488, 200310528341893369967935488, 211438891027554112743931904, 38845436263007567977235087360, 198602287451032434233585958912,
    448569005449029628854297165824, 175971202209107178462520541184, 8336750522071884076911951872, 175710074294328179809553743872, 173901521081411410817884094464, 38855107669564485010632736768,
    198602287451032434233585958912, 8327079115514967043514302464, 601967777799760601599809945600, 26300808729733912480251262271488, 259343903873019897193902899200, 304660952156887725602987048960,
    3604893033962496477906547507200, 8086839428388272589082397245440, 26300804347538163101303356522496, 3604893033962496477906547507200, 259343903873019897193902899200, 252866194476902727852931153920,
    252832547615712281630783569920, 252866194476902727852931153920, 8086839428388272589082397245440, 252832547615712281630783569920, 601972159995509980547715694592, 304660952156887725602987048960,
    275579373022915035987292717056, 32379470383494566506400514572288, 2699577901942575114725321867264, 316331023472856142089017450561536
  ]
def negativeScales : Array ℕ := #[
    10, 15, 14, 8, 15, 10,
    10, 9, 10, 14, 9, 10,
    10, 26, 33, 36, 32, 26,
    40, 25, 45, 29, 24, 46,
    24, 24, 30, 24, 29, 30,
    41, 24, 24, 25, 33, 35,
    37, 34, 31, 36, 35, 33,
    35, 31, 49, 55, 29, 32,
    36, 32, 54, 36, 29, 32,
    32, 32, 32, 32, 48, 32,
    45, 52, 34, 57
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    10446049406716591, 15994684922143517, 14117561939394141, 8661778097800657, 15994684922143517, 10621136113284685,
    10621136113284685, 9398743691938200, 10621136113284685, 14117561939394141, 9398743691938200, 10621136113284685,
    10446049406716591, 26416334906415918, 33128493141032349, 36558644644174252, 32128494241555487, 26416334906415918,
    40625337397311928, 25450371230415368, 45801807916194597, 29426445391169860, 24372368718414050, 46801762017235219,
    24372368718414050, 24372368718414050, 30793030767446857, 24372368718414050, 29426445391169860, 30793030767446857,
    41626996293121481, 24372368718414050, 24372368718414050, 25450371230415368, 33971731786093165, 35325796991292927,
    37501244690415237, 34151254102019530, 31751543725332138, 36149111662020061, 35134185303394753, 33972090931424563,
    35325796991292927, 31749869093243625, 49925601022902555, 55374878103475928, 29710781209997096, 32943119365269214,
    36507799298414270, 32673418812365766, 54374877863096528, 36507799298414270, 29710781209997096, 32674288928669062,
    32674096948124685, 32674288928669062, 32673418812365766, 32674096948124685, 48925611525374699, 32943119365269214,
    45798382659445678, 52674850329864201, 34090576695978742, 57963134101338692
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
noncomputable def negativeCeiling : ℝ := 28938696453 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 15300467404497650492375040, coefficient := (-15300467404497650492375040) }, { argument := 616693838997946968456560640, coefficient := (-616693838997946968456560640) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 167880128466015887346892800, coefficient := (-167880128466015887346892800) }, { argument := 12750389503748042076979200, coefficient := (-12750389503748042076979200) }, { argument := 14875454421039382423142400, coefficient := (-14875454421039382423142400) }, { argument := 13175402487206310146211840, coefficient := (-13175402487206310146211840) }, { argument := 206508968697896115296534528, coefficient := (-206508968697896115296534528) }, { argument := 21652092915183546490937147392, coefficient := (-21652092915183546490937147392) }, { argument := 233387920384270480699293696000, coefficient := (-233387920384270480699293696000) }, { argument := 21652109431937021488626925568, coefficient := (-21652109431937021488626925568) }, { argument := 206508968697896115296534528, coefficient := (-206508968697896115296534528) }, { argument := 7638444282614496200595865600, coefficient := (-7638444282614496200595865600) }, { argument := 211438891027554112743931904, coefficient := (-211438891027554112743931904) }, { argument := 276234432822891301910666543104, coefficient := (-276234432822891301910666543104) }, { argument := 1663690221506281045011464192, coefficient := (-1663690221506281045011464192) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 276225644637728420611452043264, coefficient := (-276225644637728420611452043264) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 8579967630644432680293236736, coefficient := (-8579967630644432680293236736) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 1663690221506281045011464192, coefficient := (-1663690221506281045011464192) }, { argument := 8579967630644432680293236736, coefficient := (-8579967630644432680293236736) }, { argument := 7647232467777377499810365440, coefficient := (-7647232467777377499810365440) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 200310528341893369967935488, coefficient := (-200310528341893369967935488) }, { argument := 211438891027554112743931904, coefficient := (-211438891027554112743931904) }, { argument := 38845436263007567977235087360, coefficient := (-38845436263007567977235087360) }, { argument := 198602287451032434233585958912, coefficient := (-198602287451032434233585958912) }, { argument := 448569005449029628854297165824, coefficient := (-448569005449029628854297165824) }, { argument := 175971202209107178462520541184, coefficient := (-175971202209107178462520541184) }, { argument := 8336750522071884076911951872, coefficient := (-8336750522071884076911951872) }, { argument := 175710074294328179809553743872, coefficient := (-175710074294328179809553743872) }, { argument := 173901521081411410817884094464, coefficient := (-173901521081411410817884094464) }, { argument := 38855107669564485010632736768, coefficient := (-38855107669564485010632736768) }, { argument := 198602287451032434233585958912, coefficient := (-198602287451032434233585958912) }, { argument := 8327079115514967043514302464, coefficient := (-8327079115514967043514302464) }, { argument := 601967777799760601599809945600, coefficient := (-601967777799760601599809945600) }, { argument := 26300808729733912480251262271488, coefficient := (-26300808729733912480251262271488) }, { argument := 259343903873019897193902899200, coefficient := (-259343903873019897193902899200) }, { argument := 304660952156887725602987048960, coefficient := (-304660952156887725602987048960) }, { argument := 3604893033962496477906547507200, coefficient := (-3604893033962496477906547507200) }, { argument := 8086839428388272589082397245440, coefficient := (-8086839428388272589082397245440) }, { argument := 26300804347538163101303356522496, coefficient := (-26300804347538163101303356522496) }, { argument := 3604893033962496477906547507200, coefficient := (-3604893033962496477906547507200) }, { argument := 259343903873019897193902899200, coefficient := (-259343903873019897193902899200) }, { argument := 252866194476902727852931153920, coefficient := (-252866194476902727852931153920) }, { argument := 252832547615712281630783569920, coefficient := (-252832547615712281630783569920) }, { argument := 252866194476902727852931153920, coefficient := (-252866194476902727852931153920) }, { argument := 8086839428388272589082397245440, coefficient := (-8086839428388272589082397245440) }, { argument := 252832547615712281630783569920, coefficient := (-252832547615712281630783569920) }, { argument := 601972159995509980547715694592, coefficient := (-601972159995509980547715694592) }, { argument := 304660952156887725602987048960, coefficient := (-304660952156887725602987048960) }, { argument := 275579373022915035987292717056, coefficient := (-275579373022915035987292717056) }, { argument := 32379470383494566506400514572288, coefficient := (-32379470383494566506400514572288) }, { argument := 2699577901942575114725321867264, coefficient := (-2699577901942575114725321867264) }, { argument := 316331023472856142089017450561536, coefficient := (-316331023472856142089017450561536) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk15
