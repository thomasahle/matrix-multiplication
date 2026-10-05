import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 2,
parent chunk 7, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-4265801561070547370442039471636480)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    789410727, 126027206739, 5030248013721, 126027206739, 3157282611, 71706791799,
    599955, 2671118038153, 14845695, 472305, 5341832104847, 242535,
    242535, 8207895, 446775, 14845695, 8207895, 143817555057,
    472305, 446775, 599955, 966231, 154256067, 6156974313,
    154256067, 3864483, 20760514263, 42159, 728103792937, 1043211,
    33189, 1456097614319, 17043, 17043, 576771, 31395,
    1043211, 576771, 41631000081, 33189, 31395, 42159,
    17487413195, 240045918439, 69949650925, 68593978371189, 3348080332747659, 3529236825,
    3152058381, 143817555057, 41631000081, 1674040511087799, 143817555057, 3529236825,
    3526975833, 1517859549, 3526975833, 41631000081, 1517859549, 34296644471625,
    3152058381, 32978755122583, 3591010458699675, 31414720257
  ]
def negativeCoefficients : Array ℕ := #[
    14562057650009998728030584832, 2324791629038816716148623540224, 23197924434099275008162381430784, 2324791629038816716148623540224, 14560396073372617395450937344, 330689209165731981831538999296,
    2833207383230057994182983680, 12318357710119384184416802701312, 70106812482905477600740638720, 2230397301691747782654689280, 12317426215354727178028233785344, 2290678309845578803807518720,
    2290678309845578803807518720, 38760688242913346601269329920, 2109835285384085740349030400, 70106812482905477600740638720, 38760688242913346601269329920, 331620703930388988220107915264,
    2230397301691747782654689280, 2109835285384085740349030400, 2833207383230057994182983680, 570362111138702520559337472, 91056710072511793043764936704, 908609035362517503379677118464,
    91056710072511793043764936704, 570297031025610473261236224, 95740973362039467410825674752, 6370887953641643922054709248, 3357786081851512808823794434048, 157645589150749614496800571392,
    5015379878398740959915409408, 3357532504710203699572598898688, 5150930685923031256129339392, 5150930685923031256129339392, 87159169238118660465556979712, 4744278263350160367487549440,
    157645589150749614496800571392, 87159169238118660465556979712, 95994550503348576662021210112, 5015379878398740959915409408, 4744278263350160367487549440, 6370887953641643922054709248,
    161292917859688232763585986560, 553508202922848703923699580928, 161292913582349450672183705600, 19307488464521665159819689984, 942400833685552708030304354304, 8137866060785782989678182400,
    7268151782462284241370611712, 331620703930388988220107915264, 95994550503348576662021210112, 942401027742265781730869772288, 331620703930388988220107915264, 8137866060785782989678182400,
    8132652568188694901362262016, 6999891660059800693213495296, 8132652568188694901362262016, 95994550503348576662021210112, 6999891660059800693213495296, 19307294407808591459254272000,
    7268151782462284241370611712, 37130777320301908733609377792, 4043118340920852561481904947200, 144874826182014538071385571328
  ]
def negativeScales : Array ℕ := #[
    29, 36, 42, 36, 31, 36,
    19, 41, 23, 18, 42, 17,
    17, 22, 18, 23, 22, 37,
    18, 18, 19, 19, 27, 32,
    27, 21, 34, 15, 39, 19,
    15, 40, 14, 14, 19, 14,
    19, 19, 35, 15, 14, 15,
    34, 37, 36, 45, 51, 31,
    31, 37, 35, 50, 37, 31,
    31, 30, 31, 35, 30, 44,
    31, 44, 51, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    29556200882695030, 36874944262717124, 42193766671749617, 36874944262717124, 31556036257255134, 36061390720948405,
    19194494768972119, 41280580869505401, 23823541299803889, 18849359284634491, 42280471771058825, 17887833434243992,
    17887833434243992, 22968580858840259, 18769188934579560, 23823541299803889, 22968580858840259, 37065448832527565,
    18849359284634491, 18769188934579560, 19194494768972119, 19882008617699835, 27200751991803792, 32519574403604448,
    27200751991803792, 21881843992250449, 34273123130309811, 15363553026596901, 39405353168473391, 19992599577423370,
    15018417540548212, 40405244213260111, 14056891688362847, 14056891688362847, 19137639102247209, 14938247200400131,
    19992599577423370, 19137639102247209, 35276939164920073, 15018417540548212, 14938247200400131, 15363553026596901,
    34025597844951067, 37804519450168349, 36025597806692130, 45963147179263253, 51572255567170883, 31716709097695814,
    31553647109974669, 37065448832527565, 35276939164920073, 50572255864246839, 37065448832527565, 31716709097695814,
    31715784544476252, 30499391155058937, 31715784544476252, 35276939164920073, 30499391155058937, 44963132678872612,
    31553647109974669, 44906602179603197, 51673311278159047, 34870721684608192
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
noncomputable def negativeCeiling : ℝ := 17506311881 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 14562057650009998728030584832, coefficient := (-14562057650009998728030584832) }, { argument := 2324791629038816716148623540224, coefficient := (-2324791629038816716148623540224) }, { argument := 23197924434099275008162381430784, coefficient := (-23197924434099275008162381430784) }, { argument := 2324791629038816716148623540224, coefficient := (-2324791629038816716148623540224) }, { argument := 14560396073372617395450937344, coefficient := (-14560396073372617395450937344) }, { argument := 330689209165731981831538999296, coefficient := (-330689209165731981831538999296) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 12318357710119384184416802701312, coefficient := (-12318357710119384184416802701312) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 12317426215354727178028233785344, coefficient := (-12317426215354727178028233785344) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 331620703930388988220107915264, coefficient := (-331620703930388988220107915264) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 570362111138702520559337472, coefficient := (-570362111138702520559337472) }, { argument := 91056710072511793043764936704, coefficient := (-91056710072511793043764936704) }, { argument := 908609035362517503379677118464, coefficient := (-908609035362517503379677118464) }, { argument := 91056710072511793043764936704, coefficient := (-91056710072511793043764936704) }, { argument := 570297031025610473261236224, coefficient := (-570297031025610473261236224) }, { argument := 95740973362039467410825674752, coefficient := (-95740973362039467410825674752) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 3357786081851512808823794434048, coefficient := (-3357786081851512808823794434048) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 3357532504710203699572598898688, coefficient := (-3357532504710203699572598898688) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 5150930685923031256129339392, coefficient := (-5150930685923031256129339392) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 157645589150749614496800571392, coefficient := (-157645589150749614496800571392) }, { argument := 87159169238118660465556979712, coefficient := (-87159169238118660465556979712) }, { argument := 95994550503348576662021210112, coefficient := (-95994550503348576662021210112) }, { argument := 5015379878398740959915409408, coefficient := (-5015379878398740959915409408) }, { argument := 4744278263350160367487549440, coefficient := (-4744278263350160367487549440) }, { argument := 6370887953641643922054709248, coefficient := (-6370887953641643922054709248) }, { argument := 161292917859688232763585986560, coefficient := (-161292917859688232763585986560) }, { argument := 553508202922848703923699580928, coefficient := (-553508202922848703923699580928) }, { argument := 161292913582349450672183705600, coefficient := (-161292913582349450672183705600) }, { argument := 19307488464521665159819689984, coefficient := (-19307488464521665159819689984) }, { argument := 942400833685552708030304354304, coefficient := (-942400833685552708030304354304) }, { argument := 8137866060785782989678182400, coefficient := (-8137866060785782989678182400) }, { argument := 7268151782462284241370611712, coefficient := (-7268151782462284241370611712) }, { argument := 331620703930388988220107915264, coefficient := (-331620703930388988220107915264) }, { argument := 95994550503348576662021210112, coefficient := (-95994550503348576662021210112) }, { argument := 942401027742265781730869772288, coefficient := (-942401027742265781730869772288) }, { argument := 331620703930388988220107915264, coefficient := (-331620703930388988220107915264) }, { argument := 8137866060785782989678182400, coefficient := (-8137866060785782989678182400) }, { argument := 8132652568188694901362262016, coefficient := (-8132652568188694901362262016) }, { argument := 6999891660059800693213495296, coefficient := (-6999891660059800693213495296) }, { argument := 8132652568188694901362262016, coefficient := (-8132652568188694901362262016) }, { argument := 95994550503348576662021210112, coefficient := (-95994550503348576662021210112) }, { argument := 6999891660059800693213495296, coefficient := (-6999891660059800693213495296) }, { argument := 19307294407808591459254272000, coefficient := (-19307294407808591459254272000) }, { argument := 7268151782462284241370611712, coefficient := (-7268151782462284241370611712) }, { argument := 37130777320301908733609377792, coefficient := (-37130777320301908733609377792) }, { argument := 4043118340920852561481904947200, coefficient := (-4043118340920852561481904947200) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }] }

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


end Parent1

namespace Parent1

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-7983642835839221851941020580708352)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    36562226197301785, 32236020133, 1026624845, 31414720257, 17863272303, 32236020133,
    503251499019, 615974907, 1795505863231887, 31414720257, 1026624845, 615974907,
    1026624845, 15810022613, 17863272303, 32978658784663, 52164202881783, 37835,
    7497334777147999, 936215, 29785, 59978660818858217, 15295, 15295,
    517615, 28175, 936215, 517615, 1669275504991551, 29785,
    28175, 37835, 49277781, 7867059417, 314005689963, 7867059417,
    197088633, 71706791799, 599955, 2671118038153, 14845695, 472305,
    5341832104847, 242535, 242535, 8207895, 446775, 14845695,
    8207895, 143817555057, 472305, 446775, 599955, 52221325473569,
    88813427975103, 52221325295969, 1759746255, 5405, 64454018865, 133745,
    4255, 128898293415, 2185, 2185
  ]
def negativeCoefficients : Array ℕ := #[
    41165407069501026472407429283840, 148662403337099885471944671232, 4734471443856684250698874880, 144874826182014538071385571328, 82379803123106305962160422912, 148662403337099885471944671232,
    2320837901778546619692588466176, 90901851722048337613418397696, 4043119768296333524005055102976, 144874826182014538071385571328, 4734471443856684250698874880, 90901851722048337613418397696,
    4734471443856684250698874880, 145821720470785874921525346304, 82379803123106305962160422912, 37130668853446755321445875712, 939706738641907489623320297472, 178670735879373026660188160,
    33764994108635588965790598037504, 4421150336759804893740400640, 140655685692272382689935360, 33764984314248904320728594120704, 144457190710982447086960640, 144457190710982447086960640,
    2444367727030571407287255040, 133052675654852253895884800, 4421150336759804893740400640, 2444367727030571407287255040, 939718567782330702406103334912, 140655685692272382689935360,
    133052675654852253895884800, 178670735879373026660188160, 909014614627307142141444096, 145121631678065670163500367872, 1448095650109012271011360407552, 145121631678065670163500367872,
    908910893197066691760095232, 330689209165731981831538999296, 2833207383230057994182983680, 12318357710119384184416802701312, 70106812482905477600740638720, 2230397301691747782654689280,
    12317426215354727178028233785344, 2290678309845578803807518720, 2290678309845578803807518720, 38760688242913346601269329920, 2109835285384085740349030400, 70106812482905477600740638720,
    38760688242913346601269329920, 331620703930388988220107915264, 2230397301691747782654689280, 2109835285384085740349030400, 2833207383230057994182983680, 940735767774234955845673680896,
    3199840969073362047181158088704, 940735764574877780561673322496, 8115397200163456853496299520, 204195126719283459040215040, 297241697631175597597088808960, 5052743242011205592846172160,
    160749355076882723074211840, 297219228770553271460906926080, 165093932241122796670812160, 165093932241122796670812160
  ]
def negativeScales : Array ℕ := #[
    55, 34, 29, 34, 34, 34,
    38, 29, 50, 34, 29, 29,
    29, 33, 34, 44, 45, 15,
    52, 19, 14, 55, 13, 13,
    18, 14, 19, 18, 50, 14,
    14, 15, 25, 32, 38, 32,
    27, 36, 19, 41, 23, 18,
    42, 17, 17, 22, 18, 23,
    22, 37, 18, 18, 19, 45,
    46, 45, 30, 12, 35, 17,
    12, 36, 11, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    55021203433944650, 34907954593281557, 29935261942353534, 34870721684608192, 34056277335205052, 34907954593281557,
    38872488610867750, 29198296340077480, 50673311787485510, 34870721684608192, 29935261942353534, 29198296340077480,
    29935261942353534, 33880120383095956, 34056277335205052, 44906597965179272, 45568125346060039, 15207433824679617,
    52735299247460520, 19836480355810319, 14862298340817341, 55735298828970437, 13900772490874059, 13900772490874059,
    18981519917909408, 14782127990393705, 19836480355810319, 18981519917909408, 50568143506762855, 14862298340817341,
    14782127990393705, 15207433824679617, 25554433956520759, 32873177336453864, 38191999745575429, 32873177336453864,
    27554269331080864, 36061390720948405, 19194494768972119, 41280580869505401, 23823541299803889, 18849359284634491,
    42280471771058825, 17887833434243992, 17887833434243992, 22968580858840259, 18769188934579560, 23823541299803889,
    22968580858840259, 37065448832527565, 18849359284634491, 18769188934579560, 19194494768972119, 45569704309914944,
    46335843052098982, 45569704305008469, 30712720269852486, 12400078902622020, 35907551270811095, 17029125432417594,
    12054943416573326, 36907442211610582, 11093417564387961, 11093417564387961
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
noncomputable def negativeCeiling : ℝ := 93064660011 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 41165407069501026472407429283840, coefficient := (-41165407069501026472407429283840) }, { argument := 148662403337099885471944671232, coefficient := (-148662403337099885471944671232) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }, { argument := 82379803123106305962160422912, coefficient := (-82379803123106305962160422912) }, { argument := 148662403337099885471944671232, coefficient := (-148662403337099885471944671232) }, { argument := 2320837901778546619692588466176, coefficient := (-2320837901778546619692588466176) }, { argument := 90901851722048337613418397696, coefficient := (-90901851722048337613418397696) }, { argument := 4043119768296333524005055102976, coefficient := (-4043119768296333524005055102976) }, { argument := 144874826182014538071385571328, coefficient := (-144874826182014538071385571328) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 90901851722048337613418397696, coefficient := (-90901851722048337613418397696) }, { argument := 4734471443856684250698874880, coefficient := (-4734471443856684250698874880) }, { argument := 145821720470785874921525346304, coefficient := (-145821720470785874921525346304) }, { argument := 82379803123106305962160422912, coefficient := (-82379803123106305962160422912) }, { argument := 37130668853446755321445875712, coefficient := (-37130668853446755321445875712) }, { argument := 939706738641907489623320297472, coefficient := (-939706738641907489623320297472) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 33764994108635588965790598037504, coefficient := (-33764994108635588965790598037504) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 33764984314248904320728594120704, coefficient := (-33764984314248904320728594120704) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 144457190710982447086960640, coefficient := (-144457190710982447086960640) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 4421150336759804893740400640, coefficient := (-4421150336759804893740400640) }, { argument := 2444367727030571407287255040, coefficient := (-2444367727030571407287255040) }, { argument := 939718567782330702406103334912, coefficient := (-939718567782330702406103334912) }, { argument := 140655685692272382689935360, coefficient := (-140655685692272382689935360) }, { argument := 133052675654852253895884800, coefficient := (-133052675654852253895884800) }, { argument := 178670735879373026660188160, coefficient := (-178670735879373026660188160) }, { argument := 909014614627307142141444096, coefficient := (-909014614627307142141444096) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 1448095650109012271011360407552, coefficient := (-1448095650109012271011360407552) }, { argument := 145121631678065670163500367872, coefficient := (-145121631678065670163500367872) }, { argument := 908910893197066691760095232, coefficient := (-908910893197066691760095232) }, { argument := 330689209165731981831538999296, coefficient := (-330689209165731981831538999296) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 12318357710119384184416802701312, coefficient := (-12318357710119384184416802701312) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 12317426215354727178028233785344, coefficient := (-12317426215354727178028233785344) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 2290678309845578803807518720, coefficient := (-2290678309845578803807518720) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 70106812482905477600740638720, coefficient := (-70106812482905477600740638720) }, { argument := 38760688242913346601269329920, coefficient := (-38760688242913346601269329920) }, { argument := 331620703930388988220107915264, coefficient := (-331620703930388988220107915264) }, { argument := 2230397301691747782654689280, coefficient := (-2230397301691747782654689280) }, { argument := 2109835285384085740349030400, coefficient := (-2109835285384085740349030400) }, { argument := 2833207383230057994182983680, coefficient := (-2833207383230057994182983680) }, { argument := 940735767774234955845673680896, coefficient := (-940735767774234955845673680896) }, { argument := 3199840969073362047181158088704, coefficient := (-3199840969073362047181158088704) }, { argument := 940735764574877780561673322496, coefficient := (-940735764574877780561673322496) }, { argument := 8115397200163456853496299520, coefficient := (-8115397200163456853496299520) }, { argument := 204195126719283459040215040, coefficient := (-204195126719283459040215040) }, { argument := 297241697631175597597088808960, coefficient := (-297241697631175597597088808960) }, { argument := 5052743242011205592846172160, coefficient := (-5052743242011205592846172160) }, { argument := 160749355076882723074211840, coefficient := (-160749355076882723074211840) }, { argument := 297219228770553271460906926080, coefficient := (-297219228770553271460906926080) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }, { argument := 165093932241122796670812160, coefficient := (-165093932241122796670812160) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk7
