import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 21, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21

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
def constantNumerator : ℤ := (-2675113418722914604147453464674304)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8772618855, 224163225, 243044594793, 874224179829, 121522337937, 26214848847,
    200066355, 26214851457, 200066355, 10764212823, 38718553419, 5382108207,
    19218298637, 19218303219, 60357, 32191493184123, 5714836701, 431973994910689,
    59796705969, 2648338959, 863947678171403, 2648338959, 5157291657, 97430996439,
    5157291657, 59796705969, 97430996439, 4023949633431, 5157291657, 5157291657,
    5714836701, 438845906342431, 12453437955, 10318562877, 52504836496098735, 69383440035,
    14043064398698097, 277889572653, 277889572653, 198899194767, 10318562877, 147286793937,
    2127789819, 147286794111, 2127789819, 10764212823, 38718553419, 5382108207,
    6081740075, 6081741525, 2122811, 729808809, 729808983, 19,
    310545, 200066355, 2127789819, 100033479, 310545, 897802455,
    35135463209, 35135463209, 897802455, 20961888129
  ]
def negativeCoefficients : Array ℕ := #[
    647305019497535689200469278720, 16540326569249483214186086400, 560422679830614012110554791936, 2015823713544274885382617694208, 560422866790671042166074114048, 241789303805794461096792293376,
    14762291393779685281989918720, 241789327878795477287757152256, 14762291393779685281989918720, 49641169775205903170631892992, 178557811456136236933658443776, 49641186335770395343381856256,
    177257518244430051677826973696, 177257560505920724546409725952, 2280222990452505409304395776, 144977596708516204580865835008, 52710065023194797394685329408, 3890875845027047031862867263488,
    551527265730501660544390397952, 48853230997107373195074207744, 3890874441480335751838473125888, 48853230997107373195074207744, 47567619655078231795203833856, 1797284656156739677018782695424,
    47567619655078231795203833856, 551527265730501660544390397952, 1797284656156739677018782695424, 144978064557419964588997214208, 47567619655078231795203833856, 47567619655078231795203833856,
    52710065023194797394685329408, 3952772520553679677578964631552, 459450765587411695481451970560, 23792986075062391373146619904, 14778797629936192612726902620160, 639949280639609147277736673280,
    3952771224569789257641866821632, 640769728435300953876810694656, 640769728435300953876810694656, 458630317791719888882377949184, 23792986075062391373146619904, 1358480896596517334027228676096,
    157003176934951077966319190016, 1358480898201384068439959666688, 157003176934951077966319190016, 49641169775205903170631892992, 178557811456136236933658443776, 49641186335770395343381856256,
    112188302686348133973308211200, 112188329434127040852158054400, 80197532126935955405849755648, 6731298161180888038398492672, 6731299766047622451129483264, 1470053796651389076442710016,
    45828353106961061652725760, 14762291393779685281989918720, 157003176934951077966319190016, 14762335887326391069428416512, 45828353106961061652725760, 16561532116133136397794017280,
    648134897727660734955854495744, 648134897727660734955854495744, 16561532116133136397794017280, 48334823202174168876667895808
  ]
def negativeScales : Array ℕ := #[
    33, 27, 37, 39, 36, 34,
    27, 34, 27, 33, 35, 32,
    34, 34, 15, 44, 32, 48,
    35, 31, 49, 31, 32, 36,
    32, 35, 36, 41, 32, 32,
    32, 48, 33, 33, 55, 36,
    53, 38, 38, 37, 33, 37,
    30, 37, 30, 33, 35, 32,
    32, 32, 21, 29, 29, 4,
    18, 27, 30, 26, 18, 29,
    35, 35, 29, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    33030360442963945, 27739974376129735, 37822430094342231, 39669212325415913, 36822430575633080, 34609665176279716,
    27575903329864433, 34609665319917160, 27575903329864433, 33325523769272599, 35172306001325474, 32325524250563439,
    34161761571322015, 34161761915287316, 15881233482214770, 44871744733101528, 32412065128624906, 48617937792342681,
    35799346962143843, 31302440637450397, 49617937271922517, 31302440637450397, 32263966489635761, 36503661769382554,
    32263966489635761, 35799346962143843, 36503661769382554, 41871749388732828, 32263966489635761, 32263966489635761,
    32412065128624906, 48640707778037965, 33535825023371593, 33264523001553338, 55543299841312040, 36013872320175376,
    53640707305025711, 38015720744567745, 38015720744567745, 37533246479269750, 33264523001553338, 37099837124673030,
    30986708522980638, 37099837126377385, 30986708522980638, 33325523769272599, 35172306001325474, 32325524250563439,
    32501837012919924, 32501837356885226, 21017544498975078, 29442943323866103, 29442943667831405, 4247927513443586,
    18244442813970666, 27575903329864433, 30986708522980638, 26575907678140777, 18244442813970666, 29741822800529638,
    35032208867356314, 35032208867356314, 29741822800529638, 34287049621457963
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
noncomputable def negativeCeiling : ℝ := 13693904153 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 647305019497535689200469278720, coefficient := (-647305019497535689200469278720) }, { argument := 16540326569249483214186086400, coefficient := (-16540326569249483214186086400) }, { argument := 560422679830614012110554791936, coefficient := (-560422679830614012110554791936) }, { argument := 2015823713544274885382617694208, coefficient := (-2015823713544274885382617694208) }, { argument := 560422866790671042166074114048, coefficient := (-560422866790671042166074114048) }, { argument := 241789303805794461096792293376, coefficient := (-241789303805794461096792293376) }, { argument := 14762291393779685281989918720, coefficient := (-14762291393779685281989918720) }, { argument := 241789327878795477287757152256, coefficient := (-241789327878795477287757152256) }, { argument := 14762291393779685281989918720, coefficient := (-14762291393779685281989918720) }, { argument := 49641169775205903170631892992, coefficient := (-49641169775205903170631892992) }, { argument := 178557811456136236933658443776, coefficient := (-178557811456136236933658443776) }, { argument := 49641186335770395343381856256, coefficient := (-49641186335770395343381856256) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 2280222990452505409304395776, coefficient := (-2280222990452505409304395776) }, { argument := 144977596708516204580865835008, coefficient := (-144977596708516204580865835008) }, { argument := 52710065023194797394685329408, coefficient := (-52710065023194797394685329408) }, { argument := 3890875845027047031862867263488, coefficient := (-3890875845027047031862867263488) }, { argument := 551527265730501660544390397952, coefficient := (-551527265730501660544390397952) }, { argument := 48853230997107373195074207744, coefficient := (-48853230997107373195074207744) }, { argument := 3890874441480335751838473125888, coefficient := (-3890874441480335751838473125888) }, { argument := 48853230997107373195074207744, coefficient := (-48853230997107373195074207744) }, { argument := 47567619655078231795203833856, coefficient := (-47567619655078231795203833856) }, { argument := 1797284656156739677018782695424, coefficient := (-1797284656156739677018782695424) }, { argument := 47567619655078231795203833856, coefficient := (-47567619655078231795203833856) }, { argument := 551527265730501660544390397952, coefficient := (-551527265730501660544390397952) }, { argument := 1797284656156739677018782695424, coefficient := (-1797284656156739677018782695424) }, { argument := 144978064557419964588997214208, coefficient := (-144978064557419964588997214208) }, { argument := 47567619655078231795203833856, coefficient := (-47567619655078231795203833856) }, { argument := 47567619655078231795203833856, coefficient := (-47567619655078231795203833856) }, { argument := 52710065023194797394685329408, coefficient := (-52710065023194797394685329408) }, { argument := 3952772520553679677578964631552, coefficient := (-3952772520553679677578964631552) }, { argument := 459450765587411695481451970560, coefficient := (-459450765587411695481451970560) }, { argument := 23792986075062391373146619904, coefficient := (-23792986075062391373146619904) }, { argument := 14778797629936192612726902620160, coefficient := (-14778797629936192612726902620160) }, { argument := 639949280639609147277736673280, coefficient := (-639949280639609147277736673280) }, { argument := 3952771224569789257641866821632, coefficient := (-3952771224569789257641866821632) }, { argument := 640769728435300953876810694656, coefficient := (-640769728435300953876810694656) }, { argument := 640769728435300953876810694656, coefficient := (-640769728435300953876810694656) }, { argument := 458630317791719888882377949184, coefficient := (-458630317791719888882377949184) }, { argument := 23792986075062391373146619904, coefficient := (-23792986075062391373146619904) }, { argument := 1358480896596517334027228676096, coefficient := (-1358480896596517334027228676096) }, { argument := 157003176934951077966319190016, coefficient := (-157003176934951077966319190016) }, { argument := 1358480898201384068439959666688, coefficient := (-1358480898201384068439959666688) }, { argument := 157003176934951077966319190016, coefficient := (-157003176934951077966319190016) }, { argument := 49641169775205903170631892992, coefficient := (-49641169775205903170631892992) }, { argument := 178557811456136236933658443776, coefficient := (-178557811456136236933658443776) }, { argument := 49641186335770395343381856256, coefficient := (-49641186335770395343381856256) }, { argument := 112188302686348133973308211200, coefficient := (-112188302686348133973308211200) }, { argument := 112188329434127040852158054400, coefficient := (-112188329434127040852158054400) }, { argument := 80197532126935955405849755648, coefficient := (-80197532126935955405849755648) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 1470053796651389076442710016, coefficient := (-1470053796651389076442710016) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 14762291393779685281989918720, coefficient := (-14762291393779685281989918720) }, { argument := 157003176934951077966319190016, coefficient := (-157003176934951077966319190016) }, { argument := 14762335887326391069428416512, coefficient := (-14762335887326391069428416512) }, { argument := 45828353106961061652725760, coefficient := (-45828353106961061652725760) }, { argument := 16561532116133136397794017280, coefficient := (-16561532116133136397794017280) }, { argument := 648134897727660734955854495744, coefficient := (-648134897727660734955854495744) }, { argument := 648134897727660734955854495744, coefficient := (-648134897727660734955854495744) }, { argument := 16561532116133136397794017280, coefficient := (-16561532116133136397794017280) }, { argument := 48334823202174168876667895808, coefficient := (-48334823202174168876667895808) }] }

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
def constantNumerator : ℤ := (-2197048255618193298587145404940288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    75399288237, 10480947561, 897802455, 35135463209, 35135463209, 897802455,
    396009724383, 1424435202099, 198004928247, 19218298637, 19218303219, 20961888129,
    75399288237, 10480947561, 38193327671, 38193336777, 49, 642601245,
    25148174051, 25148174051, 642601245, 243044594793, 874224179829, 121522337937,
    6081740075, 6081741525, 396009724383, 1424435202099, 198004928247, 589442248069,
    589442388603, 41, 37706788465, 37706797455, 1147, 2044121307771,
    318217725, 263666115, 241656415067979, 1772927325, 65411873901909, 7100801235,
    7100801235, 5082391665, 263666115, 26214862711, 100033479, 26214865321,
    100033479, 16974297, 19218298637, 19218303219, 41, 37,
    33337095, 1304645881, 1304645881, 33337095, 20961888129, 75399288237,
    10480947561, 729808809, 729808983, 20961888129
  ]
def negativeCoefficients : Array ℕ := #[
    173858921680974757014351642624, 48334839326934332308029702144, 16561532116133136397794017280, 648134897727660734955854495744, 648134897727660734955854495744, 16561532116133136397794017280,
    1826272509098364542961668063232, 6569047905675748927190908010496, 1826273118352816123422311448576, 177257518244430051677826973696, 177257560505920724546409725952, 48334823202174168876667895808,
    173858921680974757014351642624, 48334839326934332308029702144, 176135635217566570338093891584, 176135677211579454137888145408, 1895595685155738545939283968, 11853900707962129636833361920,
    463901930639900577260336316416, 463901930639900577260336316416, 11853900707962129636833361920, 560422679830614012110554791936, 2015823713544274885382617694208, 560422866790671042166074114048,
    112188302686348133973308211200, 112188329434127040852158054400, 1826272509098364542961668063232, 6569047905675748927190908010496, 1826273118352816123422311448576, 2718322574090215286173257957376,
    2718323222188898199847789658112, 25377770805350295635432046592, 173891869163839607658627727360, 173891910622896913320844984320, 44372413283135349228415483904, 147294463359641065111374790656,
    11740161865586171652027187200, 607972668039283889122836480, 544161870425920069600429473792, 16352368312780739086752153600, 147294445465121622310552338432, 16373332887540714393273630720,
    16373332887540714393273630720, 11719197290826196345505710080, 607972668039283889122836480, 241789431678624380051404095488, 14762335887326391069428416512, 241789455751625396242368954368,
    14762335887326391069428416512, 80158851223074770141904371712, 177257518244430051677826973696, 177257560505920724546409725952, 25377770805350295635432046592, 1431368170423720942852112384,
    614960859625942324629995520, 24066468673626326906171293696, 24066468673626326906171293696, 614960859625942324629995520, 48334823202174168876667895808, 173858921680974757014351642624,
    48334839326934332308029702144, 6731298161180888038398492672, 6731299766047622451129483264, 48334823202174168876667895808
  ]
def negativeScales : Array ℕ := #[
    36, 33, 29, 35, 35, 29,
    38, 40, 37, 34, 34, 34,
    36, 33, 35, 35, 5, 29,
    34, 34, 29, 37, 39, 36,
    32, 32, 38, 40, 37, 39,
    39, 5, 35, 35, 10, 40,
    28, 27, 47, 30, 45, 32,
    32, 32, 27, 34, 26, 34,
    26, 24, 34, 34, 5, 5,
    24, 30, 30, 24, 34, 36,
    33, 29, 29, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36133831853510838, 33287050102748803, 29741822800529638, 35032208867356314, 35032208867356314, 29741822800529638,
    38526744901205096, 40373527133257327, 37526745382495936, 34161761571322015, 34161761915287316, 34287049621457963,
    36133831853510838, 33287050102748803, 35152601572036539, 35152601916001840, 5614709844123661, 29259348535042968,
    34549734602058844, 34549734602058844, 29259348535042968, 37822430094342231, 39669212325415913, 36822430575633080,
    32501837012919924, 32501837356885226, 38526744901205096, 40373527133257327, 37526745382495936, 39100559512596258,
    39100559856561560, 5357552004618085, 35134105228419149, 35134105572384451, 10163649676015826, 40894617957737114,
    28245438956356175, 27974136950119248, 47779950622245480, 30723486253285392, 45894617782466861, 32725334677683094,
    32725334677683094, 32242860412254399, 27974136950119248, 34609665939264042, 26575907678140777, 34609666082901409,
    26575907678140777, 24016848489897121, 34161761571322015, 34161761915287316, 5357552004618085, 5209453365628950,
    24990625077700368, 30281011124341907, 30281011124341907, 24990625077700368, 34287049621457963, 36133831853510838,
    33287050102748803, 29442943323866103, 29442943667831405, 34287049621457963
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
noncomputable def negativeCeiling : ℝ := 8243432169 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 173858921680974757014351642624, coefficient := (-173858921680974757014351642624) }, { argument := 48334839326934332308029702144, coefficient := (-48334839326934332308029702144) }, { argument := 16561532116133136397794017280, coefficient := (-16561532116133136397794017280) }, { argument := 648134897727660734955854495744, coefficient := (-648134897727660734955854495744) }, { argument := 648134897727660734955854495744, coefficient := (-648134897727660734955854495744) }, { argument := 16561532116133136397794017280, coefficient := (-16561532116133136397794017280) }, { argument := 1826272509098364542961668063232, coefficient := (-1826272509098364542961668063232) }, { argument := 6569047905675748927190908010496, coefficient := (-6569047905675748927190908010496) }, { argument := 1826273118352816123422311448576, coefficient := (-1826273118352816123422311448576) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 48334823202174168876667895808, coefficient := (-48334823202174168876667895808) }, { argument := 173858921680974757014351642624, coefficient := (-173858921680974757014351642624) }, { argument := 48334839326934332308029702144, coefficient := (-48334839326934332308029702144) }, { argument := 176135635217566570338093891584, coefficient := (-176135635217566570338093891584) }, { argument := 176135677211579454137888145408, coefficient := (-176135677211579454137888145408) }, { argument := 1895595685155738545939283968, coefficient := (-1895595685155738545939283968) }, { argument := 11853900707962129636833361920, coefficient := (-11853900707962129636833361920) }, { argument := 463901930639900577260336316416, coefficient := (-463901930639900577260336316416) }, { argument := 463901930639900577260336316416, coefficient := (-463901930639900577260336316416) }, { argument := 11853900707962129636833361920, coefficient := (-11853900707962129636833361920) }, { argument := 560422679830614012110554791936, coefficient := (-560422679830614012110554791936) }, { argument := 2015823713544274885382617694208, coefficient := (-2015823713544274885382617694208) }, { argument := 560422866790671042166074114048, coefficient := (-560422866790671042166074114048) }, { argument := 112188302686348133973308211200, coefficient := (-112188302686348133973308211200) }, { argument := 112188329434127040852158054400, coefficient := (-112188329434127040852158054400) }, { argument := 1826272509098364542961668063232, coefficient := (-1826272509098364542961668063232) }, { argument := 6569047905675748927190908010496, coefficient := (-6569047905675748927190908010496) }, { argument := 1826273118352816123422311448576, coefficient := (-1826273118352816123422311448576) }, { argument := 2718322574090215286173257957376, coefficient := (-2718322574090215286173257957376) }, { argument := 2718323222188898199847789658112, coefficient := (-2718323222188898199847789658112) }, { argument := 25377770805350295635432046592, coefficient := (-25377770805350295635432046592) }, { argument := 173891869163839607658627727360, coefficient := (-173891869163839607658627727360) }, { argument := 173891910622896913320844984320, coefficient := (-173891910622896913320844984320) }, { argument := 44372413283135349228415483904, coefficient := (-44372413283135349228415483904) }, { argument := 147294463359641065111374790656, coefficient := (-147294463359641065111374790656) }, { argument := 11740161865586171652027187200, coefficient := (-11740161865586171652027187200) }, { argument := 607972668039283889122836480, coefficient := (-607972668039283889122836480) }, { argument := 544161870425920069600429473792, coefficient := (-544161870425920069600429473792) }, { argument := 16352368312780739086752153600, coefficient := (-16352368312780739086752153600) }, { argument := 147294445465121622310552338432, coefficient := (-147294445465121622310552338432) }, { argument := 16373332887540714393273630720, coefficient := (-16373332887540714393273630720) }, { argument := 16373332887540714393273630720, coefficient := (-16373332887540714393273630720) }, { argument := 11719197290826196345505710080, coefficient := (-11719197290826196345505710080) }, { argument := 607972668039283889122836480, coefficient := (-607972668039283889122836480) }, { argument := 241789431678624380051404095488, coefficient := (-241789431678624380051404095488) }, { argument := 14762335887326391069428416512, coefficient := (-14762335887326391069428416512) }, { argument := 241789455751625396242368954368, coefficient := (-241789455751625396242368954368) }, { argument := 14762335887326391069428416512, coefficient := (-14762335887326391069428416512) }, { argument := 80158851223074770141904371712, coefficient := (-80158851223074770141904371712) }, { argument := 177257518244430051677826973696, coefficient := (-177257518244430051677826973696) }, { argument := 177257560505920724546409725952, coefficient := (-177257560505920724546409725952) }, { argument := 25377770805350295635432046592, coefficient := (-25377770805350295635432046592) }, { argument := 1431368170423720942852112384, coefficient := (-1431368170423720942852112384) }, { argument := 614960859625942324629995520, coefficient := (-614960859625942324629995520) }, { argument := 24066468673626326906171293696, coefficient := (-24066468673626326906171293696) }, { argument := 24066468673626326906171293696, coefficient := (-24066468673626326906171293696) }, { argument := 614960859625942324629995520, coefficient := (-614960859625942324629995520) }, { argument := 48334823202174168876667895808, coefficient := (-48334823202174168876667895808) }, { argument := 173858921680974757014351642624, coefficient := (-173858921680974757014351642624) }, { argument := 48334839326934332308029702144, coefficient := (-48334839326934332308029702144) }, { argument := 6731298161180888038398492672, coefficient := (-6731298161180888038398492672) }, { argument := 6731299766047622451129483264, coefficient := (-6731299766047622451129483264) }, { argument := 48334823202174168876667895808, coefficient := (-48334823202174168876667895808) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk21
