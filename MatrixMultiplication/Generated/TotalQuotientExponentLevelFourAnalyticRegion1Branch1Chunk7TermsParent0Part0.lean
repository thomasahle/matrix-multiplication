import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 7, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7

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
def constantNumerator : ℤ := (-3738276862842531157419643094695936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    845633, 2211921, 4389, 520404637, 171, 285,
    8721, 285, 171, 139707, 8949, 70781503,
    8721, 285, 8949, 285, 8721, 285,
    845633, 1299222209728665, 72519507515, 10381179400334949, 818434441955, 72519507515,
    20762355864658589, 72519507515, 72519507515, 3006451582979, 18647873361, 818434441955,
    3006451582979, 1299224675979417, 72519507515, 18647873361, 72519507515, 3684907257843357,
    59570513721, 1545741873, 6712915685067245, 95954899347, 3685687431396745, 95954899347,
    99997608861, 59570513721, 2972580525, 726832275, 28444552045, 28444552045,
    726832275, 3677192205, 13659852675, 229776135, 1301363488518891, 391371225,
    1301364163611925, 391371225, 95416165, 354447275, 5962255, 71932305025,
    71932322175, 831285, 1299222882873191, 72519524805
  ]
def negativeCoefficients : Array ℕ := #[
    7986777872017013381986779136, 334256050980976272343157440512, 169791213513235438329133006848, 2457541415298744435752254308352, 105843873358900013503875121152, 5512701737442709036660162560,
    168688673165746896521800974336, 176406455598166689173125201920, 105843873358900013503875121152, 2702326391694415969770811686912, 173098834555701063751129104384, 334256197374337241302159065088,
    168688673165746896521800974336, 5512701737442709036660162560, 173098834555701063751129104384, 5512701737442709036660162560, 168688673165746896521800974336, 176406455598166689173125201920,
    7986777872017013381986779136, 365698541225343006063974154240, 83609299717541346396487024640, 11688168919753686358642630066176, 943590668240823766474639278080, 83609299717541346396487024640,
    11688167266926256712647356448768, 83609299717541346396487024640, 83609299717541346396487024640, 3466202682575785532037219221504, 85998136852328242007815225344, 943590668240823766474639278080,
    3466202682575785532037219221504, 365699235413215987901820567552, 83609299717541346396487024640, 85998136852328242007815225344, 83609299717541346396487024640, 4148836738329544702257442848768,
    137360252618836284988710715392, 7128476183811863093226504192, 15116142288919201230786144501760, 221256933859083596778222649344, 4149715135660625330399220858880, 221256933859083596778222649344,
    230578787330222186977057308672, 137360252618836284988710715392, 6854304022896022205025484800, 3351922240359270272571801600, 131177342966356664288731463680, 131177342966356664288731463680,
    3351922240359270272571801600, 135664447030949417272800706560, 503959612760603631629736345600, 135635889810916348253039493120, 366301257622952891068497002496, 3609762412694598755077324800,
    366301447644748913744596172800, 3609762412694598755077324800, 7040470304999370956273090560, 26153592678194998847052185600, 7038988293580489130896261120, 82932301339261659381130854400,
    82932321111865463388556492800, 7851264843424586042934558720, 365698730698682784819546423296, 83609319651554161048871239680
  ]
def negativeScales : Array ℕ := #[
    19, 21, 12, 28, 7, 8,
    13, 8, 7, 17, 13, 26,
    13, 8, 13, 8, 13, 8,
    19, 50, 36, 53, 39, 36,
    54, 36, 36, 41, 34, 39,
    41, 50, 36, 34, 36, 51,
    35, 30, 52, 36, 51, 36,
    36, 35, 31, 29, 34, 34,
    29, 31, 33, 27, 50, 28,
    50, 28, 26, 28, 22, 36,
    36, 19, 50, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    19689672152074280, 21076868429153798, 12099676554859644, 28955058587515140, 7417852514885912, 8154818109052105,
    13090277856857394, 8154818109052105, 7417852514885912, 17092044783031582, 13127510763056369, 26076869061007519,
    13090277856857394, 8154818109052105, 13127510763056369, 8154818109052105, 13090277856857394, 8154818109052105,
    19689672152074280, 50206569623501220, 36077650076546984, 53204819875030074, 39574075902669196, 36077650076546984,
    54204819671018126, 36077650076546984, 36077650076546984, 41451198863668810, 34118292061044329, 39574075902669196,
    41451198863668810, 50206572362096917, 36077650076546984, 34118292061044329, 36077650076546984, 51710549733270680,
    35793879350014786, 30525652274391345, 52575860945438059, 36481637419527553, 51710855150288054, 36481637419527553,
    36541174546505788, 35793879350014786, 31469068746024446, 29437047242992110, 34727433310142860, 34727433310142860,
    29437047242992110, 31775957441840083, 33669222872785524, 27775653724117542, 50208945405996696, 28543962446909700,
    50208946154406444, 28543962446909700, 26507730366393808, 28400995797696927, 22507426648673767, 36065920783964876,
    36065921127930178, 19664983653744600, 50206570370980759, 36077650420512285
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
noncomputable def negativeCeiling : ℝ := 38374478851 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 7986777872017013381986779136, coefficient := (-7986777872017013381986779136) }, { argument := 334256050980976272343157440512, coefficient := (-334256050980976272343157440512) }, { argument := 169791213513235438329133006848, coefficient := (-169791213513235438329133006848) }, { argument := 2457541415298744435752254308352, coefficient := (-2457541415298744435752254308352) }, { argument := 105843873358900013503875121152, coefficient := (-105843873358900013503875121152) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 176406455598166689173125201920, coefficient := (-176406455598166689173125201920) }, { argument := 105843873358900013503875121152, coefficient := (-105843873358900013503875121152) }, { argument := 2702326391694415969770811686912, coefficient := (-2702326391694415969770811686912) }, { argument := 173098834555701063751129104384, coefficient := (-173098834555701063751129104384) }, { argument := 334256197374337241302159065088, coefficient := (-334256197374337241302159065088) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 173098834555701063751129104384, coefficient := (-173098834555701063751129104384) }, { argument := 5512701737442709036660162560, coefficient := (-5512701737442709036660162560) }, { argument := 168688673165746896521800974336, coefficient := (-168688673165746896521800974336) }, { argument := 176406455598166689173125201920, coefficient := (-176406455598166689173125201920) }, { argument := 7986777872017013381986779136, coefficient := (-7986777872017013381986779136) }, { argument := 365698541225343006063974154240, coefficient := (-365698541225343006063974154240) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 11688168919753686358642630066176, coefficient := (-11688168919753686358642630066176) }, { argument := 943590668240823766474639278080, coefficient := (-943590668240823766474639278080) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 11688167266926256712647356448768, coefficient := (-11688167266926256712647356448768) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 3466202682575785532037219221504, coefficient := (-3466202682575785532037219221504) }, { argument := 85998136852328242007815225344, coefficient := (-85998136852328242007815225344) }, { argument := 943590668240823766474639278080, coefficient := (-943590668240823766474639278080) }, { argument := 3466202682575785532037219221504, coefficient := (-3466202682575785532037219221504) }, { argument := 365699235413215987901820567552, coefficient := (-365699235413215987901820567552) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 85998136852328242007815225344, coefficient := (-85998136852328242007815225344) }, { argument := 83609299717541346396487024640, coefficient := (-83609299717541346396487024640) }, { argument := 4148836738329544702257442848768, coefficient := (-4148836738329544702257442848768) }, { argument := 137360252618836284988710715392, coefficient := (-137360252618836284988710715392) }, { argument := 7128476183811863093226504192, coefficient := (-7128476183811863093226504192) }, { argument := 15116142288919201230786144501760, coefficient := (-15116142288919201230786144501760) }, { argument := 221256933859083596778222649344, coefficient := (-221256933859083596778222649344) }, { argument := 4149715135660625330399220858880, coefficient := (-4149715135660625330399220858880) }, { argument := 221256933859083596778222649344, coefficient := (-221256933859083596778222649344) }, { argument := 230578787330222186977057308672, coefficient := (-230578787330222186977057308672) }, { argument := 137360252618836284988710715392, coefficient := (-137360252618836284988710715392) }, { argument := 6854304022896022205025484800, coefficient := (-6854304022896022205025484800) }, { argument := 3351922240359270272571801600, coefficient := (-3351922240359270272571801600) }, { argument := 131177342966356664288731463680, coefficient := (-131177342966356664288731463680) }, { argument := 131177342966356664288731463680, coefficient := (-131177342966356664288731463680) }, { argument := 3351922240359270272571801600, coefficient := (-3351922240359270272571801600) }, { argument := 135664447030949417272800706560, coefficient := (-135664447030949417272800706560) }, { argument := 503959612760603631629736345600, coefficient := (-503959612760603631629736345600) }, { argument := 135635889810916348253039493120, coefficient := (-135635889810916348253039493120) }, { argument := 366301257622952891068497002496, coefficient := (-366301257622952891068497002496) }, { argument := 3609762412694598755077324800, coefficient := (-3609762412694598755077324800) }, { argument := 366301447644748913744596172800, coefficient := (-366301447644748913744596172800) }, { argument := 3609762412694598755077324800, coefficient := (-3609762412694598755077324800) }, { argument := 7040470304999370956273090560, coefficient := (-7040470304999370956273090560) }, { argument := 26153592678194998847052185600, coefficient := (-26153592678194998847052185600) }, { argument := 7038988293580489130896261120, coefficient := (-7038988293580489130896261120) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }, { argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 7851264843424586042934558720, coefficient := (-7851264843424586042934558720) }, { argument := 365698730698682784819546423296, coefficient := (-365698730698682784819546423296) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }] }

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
def constantNumerator : ℤ := (-10270282677843342454021836595265536)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    10381185516614043, 818434637085, 72519524805, 20762368097213795, 72519524805, 72519524805,
    3006452299773, 18647877807, 818434637085, 3006452299773, 1299225349123943, 72519524805,
    18647877807, 72519524805, 26851303917112159, 221289613335, 5742045855, 97863258023853735,
    356448538845, 13428488541338365, 356448538845, 371466197235, 221289613335, 11042395875,
    10423181428473295, 15316297255, 10423187569181233, 15316297255, 5923141935, 22002996225,
    370118445, 811807442425, 811807635975, 17274495, 71932305025, 71932322175,
    539, 7371357166442343, 3722373387, 96588531, 26857270436288933, 5995918809,
    1843229327803325, 5995918809, 6248534967, 3722373387, 185747175, 20846359904158071,
    15316297255, 20846372185570953, 15316297255, 506269465, 71932305025, 71932322175,
    21, 35, 726832275, 28444552045, 28444552045, 726832275,
    5923141935, 22002996225, 370118445, 71932305025
  ]
def negativeCoefficients : Array ℕ := #[
    11688175806071748516731349368832, 943590893210396960408689704960, 83609319651554161048871239680, 11688174153242640153974973399040, 83609319651554161048871239680, 83609319651554161048871239680,
    3466203508983002505197490536448, 85998157355884279935981846528, 943590893210396960408689704960, 3466203508983002505197490536448, 365699424886555766657392836608, 83609319651554161048871239680,
    85998157355884279935981846528, 83609319651554161048871239680, 15115940289439782360704884932608, 510259107920111177025108049920, 26480512586672436332640337920, 55092116546186297961670319800320,
    821914371440179081555413565440, 15119133997730108996350388469760, 821914371440179081555413565440, 856542734053519959836558622720, 510259107920111177025108049920, 25462031333338881089077248000,
    11735458999321851391996151726080, 141267907809922561541710807040, 11735465913144346733957865275392, 141267907809922561541710807040, 218525366774403552373553233920, 811767280434744771906581299200,
    218479367419979028024357027840, 935950257971667298729905356800, 935950481119624515385137561600, 326305984785997087583061934080, 82932301339261659381130854400, 82932321111865463388556492800,
    166812420293704992042656989184, 4149705173500571399568035414016, 137331338433552802606202486784, 7126975647250245245032464384, 15119299141132434648823911940096, 221210359512728765874661490688,
    4150583456926712146196797849600, 221210359512728765874661490688, 230530250743748317348934713344, 137331338433552802606202486784, 6852861199279081966377369600, 11735457337049692157961308209152,
    141267907809922561541710807040, 11735464250870502027762478350336, 141267907809922561541710807040, 2390789952816346947077684592640, 82932301339261659381130854400, 82932321111865463388556492800,
    103986963299971943091526434816, 5415987671873538702683668480, 3351922240359270272571801600, 131177342966356664288731463680, 131177342966356664288731463680, 3351922240359270272571801600,
    218525366774403552373553233920, 811767280434744771906581299200, 218479367419979028024357027840, 82932301339261659381130854400
  ]
def negativeScales : Array ℕ := #[
    53, 39, 36, 54, 36, 36,
    41, 34, 39, 41, 50, 36,
    34, 36, 54, 37, 32, 56,
    38, 53, 38, 38, 37, 33,
    53, 33, 53, 33, 32, 34,
    28, 39, 39, 24, 36, 36,
    9, 52, 31, 26, 54, 32,
    50, 32, 32, 31, 27, 54,
    33, 54, 33, 28, 36, 36,
    4, 5, 29, 34, 34, 29,
    32, 34, 28, 36
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    53204820725022409, 39574076246634498, 36077650420512285, 54204820521010374, 36077650420512285, 36077650420512285,
    41451199207634112, 34118292405009631, 39574076246634498, 41451199207634112, 50206573109575037, 36077650420512285,
    34118292405009631, 36077650420512285, 54575841666339671, 37687144780801636, 32418917705694197, 56441616831385863,
    38374902850830873, 53576146447937775, 38374902850830873, 38434439977808261, 37687144780801636, 33362334177327817,
    53210645211413226, 33834348515204040, 53210646061361616, 33834348515204040, 32463715511530223, 34356980942833610,
    28463411793810185, 39562346610086300, 39562346954051602, 24042140199910751, 36065920783964876, 36065921127930178,
    9074141462752506, 52710851686827137, 31793575632291201, 26525348556671302, 54576162206133083, 32481333701807515,
    50711157000342673, 32481333701807515, 32540870828785741, 31793575632291201, 27468765028304408, 54210645007062295,
    33834348515204040, 54210645857010599, 33834348515204040, 28915330237385446, 36065920783964876, 36065921127930178,
    4392317422778766, 5129283016944967, 29437047242992110, 34727433310142860, 34727433310142860, 29437047242992110,
    32463715511530223, 34356980942833610, 28463411793810185, 36065920783964876
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
noncomputable def negativeCeiling : ℝ := 12786812631 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 11688175806071748516731349368832, coefficient := (-11688175806071748516731349368832) }, { argument := 943590893210396960408689704960, coefficient := (-943590893210396960408689704960) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }, { argument := 11688174153242640153974973399040, coefficient := (-11688174153242640153974973399040) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }, { argument := 3466203508983002505197490536448, coefficient := (-3466203508983002505197490536448) }, { argument := 85998157355884279935981846528, coefficient := (-85998157355884279935981846528) }, { argument := 943590893210396960408689704960, coefficient := (-943590893210396960408689704960) }, { argument := 3466203508983002505197490536448, coefficient := (-3466203508983002505197490536448) }, { argument := 365699424886555766657392836608, coefficient := (-365699424886555766657392836608) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }, { argument := 85998157355884279935981846528, coefficient := (-85998157355884279935981846528) }, { argument := 83609319651554161048871239680, coefficient := (-83609319651554161048871239680) }, { argument := 15115940289439782360704884932608, coefficient := (-15115940289439782360704884932608) }, { argument := 510259107920111177025108049920, coefficient := (-510259107920111177025108049920) }, { argument := 26480512586672436332640337920, coefficient := (-26480512586672436332640337920) }, { argument := 55092116546186297961670319800320, coefficient := (-55092116546186297961670319800320) }, { argument := 821914371440179081555413565440, coefficient := (-821914371440179081555413565440) }, { argument := 15119133997730108996350388469760, coefficient := (-15119133997730108996350388469760) }, { argument := 821914371440179081555413565440, coefficient := (-821914371440179081555413565440) }, { argument := 856542734053519959836558622720, coefficient := (-856542734053519959836558622720) }, { argument := 510259107920111177025108049920, coefficient := (-510259107920111177025108049920) }, { argument := 25462031333338881089077248000, coefficient := (-25462031333338881089077248000) }, { argument := 11735458999321851391996151726080, coefficient := (-11735458999321851391996151726080) }, { argument := 141267907809922561541710807040, coefficient := (-141267907809922561541710807040) }, { argument := 11735465913144346733957865275392, coefficient := (-11735465913144346733957865275392) }, { argument := 141267907809922561541710807040, coefficient := (-141267907809922561541710807040) }, { argument := 218525366774403552373553233920, coefficient := (-218525366774403552373553233920) }, { argument := 811767280434744771906581299200, coefficient := (-811767280434744771906581299200) }, { argument := 218479367419979028024357027840, coefficient := (-218479367419979028024357027840) }, { argument := 935950257971667298729905356800, coefficient := (-935950257971667298729905356800) }, { argument := 935950481119624515385137561600, coefficient := (-935950481119624515385137561600) }, { argument := 326305984785997087583061934080, coefficient := (-326305984785997087583061934080) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }, { argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 166812420293704992042656989184, coefficient := (-166812420293704992042656989184) }, { argument := 4149705173500571399568035414016, coefficient := (-4149705173500571399568035414016) }, { argument := 137331338433552802606202486784, coefficient := (-137331338433552802606202486784) }, { argument := 7126975647250245245032464384, coefficient := (-7126975647250245245032464384) }, { argument := 15119299141132434648823911940096, coefficient := (-15119299141132434648823911940096) }, { argument := 221210359512728765874661490688, coefficient := (-221210359512728765874661490688) }, { argument := 4150583456926712146196797849600, coefficient := (-4150583456926712146196797849600) }, { argument := 221210359512728765874661490688, coefficient := (-221210359512728765874661490688) }, { argument := 230530250743748317348934713344, coefficient := (-230530250743748317348934713344) }, { argument := 137331338433552802606202486784, coefficient := (-137331338433552802606202486784) }, { argument := 6852861199279081966377369600, coefficient := (-6852861199279081966377369600) }, { argument := 11735457337049692157961308209152, coefficient := (-11735457337049692157961308209152) }, { argument := 141267907809922561541710807040, coefficient := (-141267907809922561541710807040) }, { argument := 11735464250870502027762478350336, coefficient := (-11735464250870502027762478350336) }, { argument := 141267907809922561541710807040, coefficient := (-141267907809922561541710807040) }, { argument := 2390789952816346947077684592640, coefficient := (-2390789952816346947077684592640) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }, { argument := 82932321111865463388556492800, coefficient := (-82932321111865463388556492800) }, { argument := 103986963299971943091526434816, coefficient := (-103986963299971943091526434816) }, { argument := 5415987671873538702683668480, coefficient := (-5415987671873538702683668480) }, { argument := 3351922240359270272571801600, coefficient := (-3351922240359270272571801600) }, { argument := 131177342966356664288731463680, coefficient := (-131177342966356664288731463680) }, { argument := 131177342966356664288731463680, coefficient := (-131177342966356664288731463680) }, { argument := 3351922240359270272571801600, coefficient := (-3351922240359270272571801600) }, { argument := 218525366774403552373553233920, coefficient := (-218525366774403552373553233920) }, { argument := 811767280434744771906581299200, coefficient := (-811767280434744771906581299200) }, { argument := 218479367419979028024357027840, coefficient := (-218479367419979028024357027840) }, { argument := 82932301339261659381130854400, coefficient := (-82932301339261659381130854400) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
