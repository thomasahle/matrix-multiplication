import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 19, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent2

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-16271859701682360129799063232053248)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    803529, 60682171, 4897, 531324097, 3099, 743,
    19587, 19471, 3099, 4695, 9611, 30341113,
    19587, 743, 9611, 743, 19587, 9797,
    803529, 3135431899814495, 89766483507, 29079309508719189, 939263937183, 41599102113,
    116317215541804603, 41599102113, 81008777799, 1530409072473, 81008777799, 939263937183,
    1530409072473, 1567720601390857, 81008777799, 81008777799, 89766483507, 37505244347070923,
    2628628625, 2178006575, 68127486687966193, 14645216625, 37503772920794707, 58655970175,
    58655970175, 41982954325, 2178006575, 68574835, 685402295, 1370804255,
    68574835, 2628628625, 9422042875, 657348125, 6261359699368825, 68574835,
    6261359560418439, 68574835, 2178006575, 7806835525, 544659875, 89078617733,
    89078638971, 405615, 3135431830005153, 89766504909
  ]
def negativeCoefficients : Array ℕ := #[
    30356467340910105191327465472, 2292507603505315052534657712128, 378887023273781700386313207808, 20072856857710241695019193860096, 239773511359087091994524123136, 14371710143578711628907020288,
    378867680460667866319517908992, 376623914139463114571263246336, 239773511359087091994524123136, 5812128484444860390651388231680, 371807553674118431939233841152, 2292509681346567515178551738368,
    378867680460667866319517908992, 14371710143578711628907020288, 371807553674118431939233841152, 14371710143578711628907020288, 378867680460667866319517908992, 379003080152464704787085000704,
    30356467340910105191327465472, 1765091241956265753543379517440, 103493709228156153590376824832, 65480783733829530341942463823872, 1082897591679975363177357508608, 95920998796827654547178520576,
    65480771071355609508382439899136, 95920998796827654547178520576, 93396761986384821532779085824, 3528883060999080554130409783296, 93396761986384821532779085824, 1082897591679975363177357508608,
    3528883060999080554130409783296, 1765096479061228369585811488768, 93396761986384821532779085824, 93396761986384821532779085824, 103493709228156153590376824832, 21113575558238501296869763710976,
    96979279020404074627465216000, 5022141234985211007493734400, 76704730915403243372838683410432, 135078281492705675373969408000, 21112747218884842605104630595584, 135251458776670682650089881600,
    135251458776670682650089881600, 96806101736439067351344742400, 5022141234985211007493734400, 1264982431141860339991183360, 50573762893592703364109434880, 50573750534274173978709852160,
    1264982431141860339991183360, 96979279020404074627465216000, 347612027133287111245955072000, 97007461033662684394946560000, 1762416075556880070537851699200, 1264982431141860339991183360,
    1762416036445823407251190185984, 1264982431141860339991183360, 5022141234985211007493734400, 18001337119402368260951244800, 5023600660671817584738304000, 102700653985028520229531025408,
    102700678470775435069747101696, 30647402895186738293652848640, 1765091202657099926270940020736, 103493733902982195186115805184
  ]
def negativeScales : Array ℕ := #[
    19, 25, 12, 28, 11, 9,
    14, 14, 11, 12, 13, 24,
    14, 9, 13, 9, 14, 13,
    19, 51, 36, 54, 39, 35,
    56, 35, 36, 40, 36, 39,
    40, 50, 36, 36, 36, 55,
    31, 31, 55, 33, 55, 35,
    35, 35, 31, 26, 29, 30,
    26, 31, 33, 29, 52, 26,
    52, 26, 31, 32, 29, 36,
    36, 18, 51, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19615990567295763, 25854769367298069, 12257682480708767, 28985016922164209, 11597587039591505, 9537218400539495,
    14257608826845782, 14249039360063383, 11597587039591505, 12196909442541137, 13230470832204705, 24854770674901157,
    14257608826845782, 9537218400539495, 13230470832204705, 9537218400539495, 14257608826845782, 13258124324938923,
    19615990567295763, 51477585608539840, 36385457829205311, 54690842530973907, 39772739662453494, 35275833338030809,
    56690842251989920, 35275833338030809, 36237359190216174, 40477054469962784, 36237359190216174, 39772739662453494,
    40477054469962784, 50477589889074449, 36237359190216174, 36237359190216174, 36385457829205311, 55057941859526636,
    31291663185095196, 31020361163277801, 55919086509165118, 33769710482243744, 55057885257814753, 35771558906649874,
    35771558906649874, 35289084640993420, 31020361163277801, 26031175909976768, 29352375781681951, 30352375429113174,
    26031175909976768, 31291663185095196, 33133392750989882, 29292082368912040, 52475397406112196, 26031175909976768,
    52475397374096301, 26031175909976768, 31020361163277801, 32862090731350385, 29020780347094645, 36374360120321979,
    36374360464287281, 18629751479910673, 51477585576418717, 36385458173170613
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
noncomputable def negativeCeiling : ℝ := 183781469 / 976562500

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 30356467340910105191327465472, coefficient := (-30356467340910105191327465472) }, { argument := 2292507603505315052534657712128, coefficient := (-2292507603505315052534657712128) }, { argument := 378887023273781700386313207808, coefficient := (-378887023273781700386313207808) }, { argument := 20072856857710241695019193860096, coefficient := (-20072856857710241695019193860096) }, { argument := 239773511359087091994524123136, coefficient := (-239773511359087091994524123136) }, { argument := 14371710143578711628907020288, coefficient := (-14371710143578711628907020288) }, { argument := 378867680460667866319517908992, coefficient := (-378867680460667866319517908992) }, { argument := 376623914139463114571263246336, coefficient := (-376623914139463114571263246336) }, { argument := 239773511359087091994524123136, coefficient := (-239773511359087091994524123136) }, { argument := 5812128484444860390651388231680, coefficient := (-5812128484444860390651388231680) }, { argument := 371807553674118431939233841152, coefficient := (-371807553674118431939233841152) }, { argument := 2292509681346567515178551738368, coefficient := (-2292509681346567515178551738368) }, { argument := 378867680460667866319517908992, coefficient := (-378867680460667866319517908992) }, { argument := 14371710143578711628907020288, coefficient := (-14371710143578711628907020288) }, { argument := 371807553674118431939233841152, coefficient := (-371807553674118431939233841152) }, { argument := 14371710143578711628907020288, coefficient := (-14371710143578711628907020288) }, { argument := 378867680460667866319517908992, coefficient := (-378867680460667866319517908992) }, { argument := 379003080152464704787085000704, coefficient := (-379003080152464704787085000704) }, { argument := 30356467340910105191327465472, coefficient := (-30356467340910105191327465472) }, { argument := 1765091241956265753543379517440, coefficient := (-1765091241956265753543379517440) }, { argument := 103493709228156153590376824832, coefficient := (-103493709228156153590376824832) }, { argument := 65480783733829530341942463823872, coefficient := (-65480783733829530341942463823872) }, { argument := 1082897591679975363177357508608, coefficient := (-1082897591679975363177357508608) }, { argument := 95920998796827654547178520576, coefficient := (-95920998796827654547178520576) }, { argument := 65480771071355609508382439899136, coefficient := (-65480771071355609508382439899136) }, { argument := 95920998796827654547178520576, coefficient := (-95920998796827654547178520576) }, { argument := 93396761986384821532779085824, coefficient := (-93396761986384821532779085824) }, { argument := 3528883060999080554130409783296, coefficient := (-3528883060999080554130409783296) }, { argument := 93396761986384821532779085824, coefficient := (-93396761986384821532779085824) }, { argument := 1082897591679975363177357508608, coefficient := (-1082897591679975363177357508608) }, { argument := 3528883060999080554130409783296, coefficient := (-3528883060999080554130409783296) }, { argument := 1765096479061228369585811488768, coefficient := (-1765096479061228369585811488768) }, { argument := 93396761986384821532779085824, coefficient := (-93396761986384821532779085824) }, { argument := 93396761986384821532779085824, coefficient := (-93396761986384821532779085824) }, { argument := 103493709228156153590376824832, coefficient := (-103493709228156153590376824832) }, { argument := 21113575558238501296869763710976, coefficient := (-21113575558238501296869763710976) }, { argument := 96979279020404074627465216000, coefficient := (-96979279020404074627465216000) }, { argument := 5022141234985211007493734400, coefficient := (-5022141234985211007493734400) }, { argument := 76704730915403243372838683410432, coefficient := (-76704730915403243372838683410432) }, { argument := 135078281492705675373969408000, coefficient := (-135078281492705675373969408000) }, { argument := 21112747218884842605104630595584, coefficient := (-21112747218884842605104630595584) }, { argument := 135251458776670682650089881600, coefficient := (-135251458776670682650089881600) }, { argument := 135251458776670682650089881600, coefficient := (-135251458776670682650089881600) }, { argument := 96806101736439067351344742400, coefficient := (-96806101736439067351344742400) }, { argument := 5022141234985211007493734400, coefficient := (-5022141234985211007493734400) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 50573762893592703364109434880, coefficient := (-50573762893592703364109434880) }, { argument := 50573750534274173978709852160, coefficient := (-50573750534274173978709852160) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 96979279020404074627465216000, coefficient := (-96979279020404074627465216000) }, { argument := 347612027133287111245955072000, coefficient := (-347612027133287111245955072000) }, { argument := 97007461033662684394946560000, coefficient := (-97007461033662684394946560000) }, { argument := 1762416075556880070537851699200, coefficient := (-1762416075556880070537851699200) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 1762416036445823407251190185984, coefficient := (-1762416036445823407251190185984) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 5022141234985211007493734400, coefficient := (-5022141234985211007493734400) }, { argument := 18001337119402368260951244800, coefficient := (-18001337119402368260951244800) }, { argument := 5023600660671817584738304000, coefficient := (-5023600660671817584738304000) }, { argument := 102700653985028520229531025408, coefficient := (-102700653985028520229531025408) }, { argument := 102700678470775435069747101696, coefficient := (-102700678470775435069747101696) }, { argument := 30647402895186738293652848640, coefficient := (-30647402895186738293652848640) }, { argument := 1765091202657099926270940020736, coefficient := (-1765091202657099926270940020736) }, { argument := 103493733902982195186115805184, coefficient := (-103493733902982195186115805184) }] }

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


end Parent2

namespace Parent2

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-49437959943287839943388790970646528)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    29079308470603179, 939264161121, 41599112031, 116317211389346245, 41599112031, 81008797113,
    1530409437351, 81008797113, 939264161121, 1530409437351, 1567720566485239, 81008797113,
    81008797113, 89766504909, 8516105302428171, 9422042875, 7806835525, 495058752364884943,
    52494238875, 136252347278146433, 210246156725, 210246156725, 150483484775, 7806835525,
    116178916122138101, 685402295, 116178911993948683, 685402295, 14645216625, 52494238875,
    3662368125, 932066512377, 932066734599, 123180875, 41280335047, 41280344889,
    9873, 37503763764057477, 657348125, 544659875, 136249602370991183, 3662368125,
    9375573084695947, 14668253875, 14668253875, 10498788625, 544659875, 232357787308463553,
    1370804255, 232357779052096063, 1370804255, 2160317185, 41280335047, 41280344889,
    781, 749, 68574835, 685402295, 1370804255, 68574835,
    58655970175, 210246156725, 14668253875, 80388020881
  ]
def negativeCoefficients : Array ℕ := #[
    65480781396200092440269414203392, 1082897849862911261825455620096, 95921021666178619928595136512, 65480768733729370288344730173440, 95921021666178619928595136512, 93396784253910761509421580288,
    3528883902350466070004631601152, 93396784253910761509421580288, 1082897849862911261825455620096, 3528883902350466070004631601152, 1765096439760996315101592027136, 93396784253910761509421580288,
    93396784253910761509421580288, 103493733902982195186115805184, 76706257333326832120041289285632, 347612027133287111245955072000, 18001337119402368260951244800, 278693301584624810588612084105216,
    484173894935649904949723136000, 76703252553776961320918078980096, 484794630698387917648376627200, 484794630698387917648376627200, 346991291370549098547301580800, 18001337119402368260951244800,
    65402915419496157726709500608512, 50573762893592703364109434880, 65402913095532117149256406532096, 50573762893592703364109434880, 135078281492705675373969408000, 484173894935649904949723136000,
    135117535011173024692961280000, 1074599525843347199474849021952, 1074599782047869796217597722624, 2326820941722221633450541056000, 95185971986123994359077535744, 95185994680230891040253411328,
    381943187745767482939970420736, 21112742064100045485411164749824, 97007461033662684394946560000, 5023600660671817584738304000, 76701707308421767507391436292096, 135117535011173024692961280000,
    21111913725310759321599639289856, 135290762620161708057952256000, 135290762620161708057952256000, 96834233424674001029955584000, 5023600660671817584738304000, 65402902771189338875033202720768,
    50573750534274173978709852160, 65402900447228491912665867747328, 50573750534274173978709852160, 20403618933622605340000932331520, 95185971986123994359077535744, 95185994680230891040253411328,
    241707792670470498674054004736, 14487767022261716029678813184, 1264982431141860339991183360, 50573762893592703364109434880, 50573750534274173978709852160, 1264982431141860339991183360,
    135251458776670682650089881600, 484794630698387917648376627200, 135290762620161708057952256000, 92681077986489152402259705856
  ]
def negativeScales : Array ℕ := #[
    54, 39, 35, 56, 35, 36,
    40, 36, 39, 40, 50, 36,
    36, 36, 52, 33, 32, 58,
    35, 56, 37, 37, 37, 32,
    56, 29, 56, 29, 33, 35,
    31, 39, 39, 26, 35, 35,
    13, 55, 29, 29, 56, 31,
    53, 33, 33, 33, 29, 57,
    30, 57, 30, 31, 35, 35,
    9, 9, 26, 29, 30, 26,
    35, 37, 33, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    54690842479470454, 39772740006418798, 35275833681996111, 56690842200486528, 35275833681996111, 36237359534181475,
    40477054813928086, 36237359534181475, 39772740006418798, 40477054813928086, 50477589856952550, 36237359534181475,
    36237359534181475, 36385458173170613, 52919115218396839, 33133392750989882, 32862090731350385, 58780377364396190,
    35611440047802263, 56919058703243059, 37613288472195029, 37613288472195029, 37130814206888106, 32862090731350385,
    56689125888717223, 29352375781681951, 56689125837453889, 29352375781681951, 33769710482243744, 35611440047802263,
    31770129666063665, 39761641953492865, 39761642297458169, 26876203043252882, 35264735629147479, 35264735973112781,
    13269272811845506, 55057884905573365, 29292082368912040, 29020780347094645, 56919029638758417, 31770129666063665,
    53057828301665469, 33771978090469910, 33771978090469910, 33289503824810264, 29020780347094645, 57689125609713585,
    30352375429113174, 57689125558450312, 30352375429113174, 31008596003241500, 35264735629147479, 35264735973112781,
    9609178738149255, 9548821908460035, 26031175909976768, 29352375781681951, 30352375429113174, 26031175909976768,
    35771558906649874, 37613288472195029, 33771978090469910, 36226261481332843
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
noncomputable def negativeCeiling : ℝ := 663985874041 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 65480781396200092440269414203392, coefficient := (-65480781396200092440269414203392) }, { argument := 1082897849862911261825455620096, coefficient := (-1082897849862911261825455620096) }, { argument := 95921021666178619928595136512, coefficient := (-95921021666178619928595136512) }, { argument := 65480768733729370288344730173440, coefficient := (-65480768733729370288344730173440) }, { argument := 95921021666178619928595136512, coefficient := (-95921021666178619928595136512) }, { argument := 93396784253910761509421580288, coefficient := (-93396784253910761509421580288) }, { argument := 3528883902350466070004631601152, coefficient := (-3528883902350466070004631601152) }, { argument := 93396784253910761509421580288, coefficient := (-93396784253910761509421580288) }, { argument := 1082897849862911261825455620096, coefficient := (-1082897849862911261825455620096) }, { argument := 3528883902350466070004631601152, coefficient := (-3528883902350466070004631601152) }, { argument := 1765096439760996315101592027136, coefficient := (-1765096439760996315101592027136) }, { argument := 93396784253910761509421580288, coefficient := (-93396784253910761509421580288) }, { argument := 93396784253910761509421580288, coefficient := (-93396784253910761509421580288) }, { argument := 103493733902982195186115805184, coefficient := (-103493733902982195186115805184) }, { argument := 76706257333326832120041289285632, coefficient := (-76706257333326832120041289285632) }, { argument := 347612027133287111245955072000, coefficient := (-347612027133287111245955072000) }, { argument := 18001337119402368260951244800, coefficient := (-18001337119402368260951244800) }, { argument := 278693301584624810588612084105216, coefficient := (-278693301584624810588612084105216) }, { argument := 484173894935649904949723136000, coefficient := (-484173894935649904949723136000) }, { argument := 76703252553776961320918078980096, coefficient := (-76703252553776961320918078980096) }, { argument := 484794630698387917648376627200, coefficient := (-484794630698387917648376627200) }, { argument := 484794630698387917648376627200, coefficient := (-484794630698387917648376627200) }, { argument := 346991291370549098547301580800, coefficient := (-346991291370549098547301580800) }, { argument := 18001337119402368260951244800, coefficient := (-18001337119402368260951244800) }, { argument := 65402915419496157726709500608512, coefficient := (-65402915419496157726709500608512) }, { argument := 50573762893592703364109434880, coefficient := (-50573762893592703364109434880) }, { argument := 65402913095532117149256406532096, coefficient := (-65402913095532117149256406532096) }, { argument := 50573762893592703364109434880, coefficient := (-50573762893592703364109434880) }, { argument := 135078281492705675373969408000, coefficient := (-135078281492705675373969408000) }, { argument := 484173894935649904949723136000, coefficient := (-484173894935649904949723136000) }, { argument := 135117535011173024692961280000, coefficient := (-135117535011173024692961280000) }, { argument := 1074599525843347199474849021952, coefficient := (-1074599525843347199474849021952) }, { argument := 1074599782047869796217597722624, coefficient := (-1074599782047869796217597722624) }, { argument := 2326820941722221633450541056000, coefficient := (-2326820941722221633450541056000) }, { argument := 95185971986123994359077535744, coefficient := (-95185971986123994359077535744) }, { argument := 95185994680230891040253411328, coefficient := (-95185994680230891040253411328) }, { argument := 381943187745767482939970420736, coefficient := (-381943187745767482939970420736) }, { argument := 21112742064100045485411164749824, coefficient := (-21112742064100045485411164749824) }, { argument := 97007461033662684394946560000, coefficient := (-97007461033662684394946560000) }, { argument := 5023600660671817584738304000, coefficient := (-5023600660671817584738304000) }, { argument := 76701707308421767507391436292096, coefficient := (-76701707308421767507391436292096) }, { argument := 135117535011173024692961280000, coefficient := (-135117535011173024692961280000) }, { argument := 21111913725310759321599639289856, coefficient := (-21111913725310759321599639289856) }, { argument := 135290762620161708057952256000, coefficient := (-135290762620161708057952256000) }, { argument := 135290762620161708057952256000, coefficient := (-135290762620161708057952256000) }, { argument := 96834233424674001029955584000, coefficient := (-96834233424674001029955584000) }, { argument := 5023600660671817584738304000, coefficient := (-5023600660671817584738304000) }, { argument := 65402902771189338875033202720768, coefficient := (-65402902771189338875033202720768) }, { argument := 50573750534274173978709852160, coefficient := (-50573750534274173978709852160) }, { argument := 65402900447228491912665867747328, coefficient := (-65402900447228491912665867747328) }, { argument := 50573750534274173978709852160, coefficient := (-50573750534274173978709852160) }, { argument := 20403618933622605340000932331520, coefficient := (-20403618933622605340000932331520) }, { argument := 95185971986123994359077535744, coefficient := (-95185971986123994359077535744) }, { argument := 95185994680230891040253411328, coefficient := (-95185994680230891040253411328) }, { argument := 241707792670470498674054004736, coefficient := (-241707792670470498674054004736) }, { argument := 14487767022261716029678813184, coefficient := (-14487767022261716029678813184) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 50573762893592703364109434880, coefficient := (-50573762893592703364109434880) }, { argument := 50573750534274173978709852160, coefficient := (-50573750534274173978709852160) }, { argument := 1264982431141860339991183360, coefficient := (-1264982431141860339991183360) }, { argument := 135251458776670682650089881600, coefficient := (-135251458776670682650089881600) }, { argument := 484794630698387917648376627200, coefficient := (-484794630698387917648376627200) }, { argument := 135290762620161708057952256000, coefficient := (-135290762620161708057952256000) }, { argument := 92681077986489152402259705856, coefficient := (-92681077986489152402259705856) }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
