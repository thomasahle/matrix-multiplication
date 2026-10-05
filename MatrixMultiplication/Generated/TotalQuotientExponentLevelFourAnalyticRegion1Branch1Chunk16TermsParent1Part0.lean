import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 16, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-251048039524167547916873564684288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    8388607, 8388607, 8388607, 8388607, 96898359903, 96799979029,
    2663486132185, 40859644943, 3995738149, 40859644943, 81590395107, 12134289043,
    96799979029, 3995738149, 13964498427363, 519015769825821, 1070235705, 2760081555,
    2309455995, 64608439665, 129696276695913, 2309455995, 2084143215, 1070235705,
    1070235705, 2084143215, 64608439665, 2084143215, 3491110295703, 2760081555,
    46585881, 9239603175, 9239603175, 46585881, 1097506059, 603091711701,
    43329525, 23655458278815, 13711875, 1645425, 43329525, 86110575,
    13711875, 1328954925, 85013625, 2412370984365, 43329525, 1645425,
    85013625, 1645425, 43329525, 43329525, 1097506059, 8388609,
    8388609, 8388609, 8388609, 11211895892639, 348186645937, 309223954187161,
    146970927779, 14372551297, 146970927779, 293478224871
  ]
def negativeCoefficients : Array ℕ := #[
    9903519133691421481781690368, 9903519133691421481781690368, 9903519133691421481781690368, 9903519133691421481781690368, 6982262680831408174905950208, 111602777468025914166612066304,
    191924402438637594448400220160, 94215926650770212492186484736, 4606772438760057708608487424, 94215926650770212492186484736, 94067321088229565469328146432, 6994941390394968641827241984,
    111602777468025914166612066304, 4606772438760057708608487424, 7861313739235985525368160256, 292179903448372322153269297152, 4935591037170278484745912320, 6364314758456411730330255360,
    85203887378518491736666275840, 148976918937744984789567406080, 292050051699527265477589991424, 85203887378518491736666275840, 4805707062507902735147335680, 4935591037170278484745912320,
    4935591037170278484745912320, 4805707062507902735147335680, 148976918937744984789567406080, 4805707062507902735147335680, 7861281513418666451448889344, 6364314758456411730330255360,
    107419728031911050018291712, 21305074388982400892377497600, 21305074388982400892377497600, 107419728031911050018291712, 158167292107176371130728448, 21728668864694865618762989568,
    799288658510399859484262400, 213069426179499097344945684480, 505878897791392316129280000, 30352733867483538967756800, 799288658510399859484262400, 794229869532485936322969600,
    505878897791392316129280000, 12257445693485435819812454400, 784112291576658090000384000, 21728706132531221264156590080, 799288658510399859484262400, 30352733867483538967756800,
    784112291576658090000384000, 30352733867483538967756800, 799288658510399859484262400, 799288658510399859484262400, 158167292107176371130728448, 9903521494874662916604297216,
    9903521494874662916604297216, 9903521494874662916604297216, 9903521494874662916604297216, 25246945082102897513146089472, 401431871717697542418451136512, 696310442425664802959736700928,
    338891886376857845397201092608, 16570423466376329979989327872, 338891886376857845397201092608, 338357356587619899268814340096
  ]
def negativeScales : Array ℕ := #[
    22, 22, 22, 22, 36, 36,
    41, 35, 31, 35, 36, 33,
    36, 31, 43, 48, 29, 31,
    31, 35, 46, 31, 30, 29,
    29, 30, 35, 30, 41, 31,
    25, 33, 33, 25, 30, 39,
    25, 44, 23, 20, 25, 26,
    23, 30, 26, 41, 25, 20,
    26, 20, 25, 25, 30, 23,
    23, 23, 23, 43, 38, 48,
    37, 33, 37, 38
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    22999999851693669, 22999999851693669, 22999999851693669, 22999999851693669, 36495753195733688, 36494287683824534,
    41276452907972411, 35249957616449446, 31895814900748032, 35249957616449446, 36247680275738380, 33498370531266043,
    36494287683824534, 31895814900748032, 43666828989831894, 48882771705855628, 29995281441714674, 31362063750430195,
    31104905910933069, 35911003587643887, 46882130395061992, 31104905910933069, 30956807283632447, 29995281441714674,
    29995281441714674, 30956807283632447, 35911003587643887, 30956807283632447, 41666823075792116, 31362063750430195,
    25473389441029040, 33105183745697582, 33105183745697582, 25473389441029040, 30031581758453158, 39133586452114240,
    25368847085360887, 44427238344085982, 23708922527047674, 20650028837926260, 25368847085360887, 26359687086075410,
    23708922527047674, 30307645026635128, 26341190742458020, 41133588926544539, 25368847085360887, 20650028837926260,
    26341190742458020, 20650028837926260, 25368847085360887, 25368847085360887, 30031581758453158, 23000000171982641,
    23000000171982641, 23000000171982641, 23000000171982641, 43350095487026003, 38341069915877186, 48135645411102529,
    37096739848502321, 33742597128940913, 37096739848502321, 38094462507791255
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
noncomputable def negativeCeiling : ℝ := 265495963 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 9903519133691421481781690368, coefficient := (-9903519133691421481781690368) }, { argument := 6982262680831408174905950208, coefficient := (-6982262680831408174905950208) }, { argument := 111602777468025914166612066304, coefficient := (-111602777468025914166612066304) }, { argument := 191924402438637594448400220160, coefficient := (-191924402438637594448400220160) }, { argument := 94215926650770212492186484736, coefficient := (-94215926650770212492186484736) }, { argument := 4606772438760057708608487424, coefficient := (-4606772438760057708608487424) }, { argument := 94215926650770212492186484736, coefficient := (-94215926650770212492186484736) }, { argument := 94067321088229565469328146432, coefficient := (-94067321088229565469328146432) }, { argument := 6994941390394968641827241984, coefficient := (-6994941390394968641827241984) }, { argument := 111602777468025914166612066304, coefficient := (-111602777468025914166612066304) }, { argument := 4606772438760057708608487424, coefficient := (-4606772438760057708608487424) }, { argument := 7861313739235985525368160256, coefficient := (-7861313739235985525368160256) }, { argument := 292179903448372322153269297152, coefficient := (-292179903448372322153269297152) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 6364314758456411730330255360, coefficient := (-6364314758456411730330255360) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 148976918937744984789567406080, coefficient := (-148976918937744984789567406080) }, { argument := 292050051699527265477589991424, coefficient := (-292050051699527265477589991424) }, { argument := 85203887378518491736666275840, coefficient := (-85203887378518491736666275840) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 4935591037170278484745912320, coefficient := (-4935591037170278484745912320) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 148976918937744984789567406080, coefficient := (-148976918937744984789567406080) }, { argument := 4805707062507902735147335680, coefficient := (-4805707062507902735147335680) }, { argument := 7861281513418666451448889344, coefficient := (-7861281513418666451448889344) }, { argument := 6364314758456411730330255360, coefficient := (-6364314758456411730330255360) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 21305074388982400892377497600, coefficient := (-21305074388982400892377497600) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 158167292107176371130728448, coefficient := (-158167292107176371130728448) }, { argument := 21728668864694865618762989568, coefficient := (-21728668864694865618762989568) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 213069426179499097344945684480, coefficient := (-213069426179499097344945684480) }, { argument := 505878897791392316129280000, coefficient := (-505878897791392316129280000) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 794229869532485936322969600, coefficient := (-794229869532485936322969600) }, { argument := 505878897791392316129280000, coefficient := (-505878897791392316129280000) }, { argument := 12257445693485435819812454400, coefficient := (-12257445693485435819812454400) }, { argument := 784112291576658090000384000, coefficient := (-784112291576658090000384000) }, { argument := 21728706132531221264156590080, coefficient := (-21728706132531221264156590080) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 784112291576658090000384000, coefficient := (-784112291576658090000384000) }, { argument := 30352733867483538967756800, coefficient := (-30352733867483538967756800) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 799288658510399859484262400, coefficient := (-799288658510399859484262400) }, { argument := 158167292107176371130728448, coefficient := (-158167292107176371130728448) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 9903521494874662916604297216, coefficient := (-9903521494874662916604297216) }, { argument := 25246945082102897513146089472, coefficient := (-25246945082102897513146089472) }, { argument := 401431871717697542418451136512, coefficient := (-401431871717697542418451136512) }, { argument := 696310442425664802959736700928, coefficient := (-696310442425664802959736700928) }, { argument := 338891886376857845397201092608, coefficient := (-338891886376857845397201092608) }, { argument := 16570423466376329979989327872, coefficient := (-16570423466376329979989327872) }, { argument := 338891886376857845397201092608, coefficient := (-338891886376857845397201092608) }, { argument := 338357356587619899268814340096, coefficient := (-338357356587619899268814340096) }] }

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


end Parent1

namespace Parent1

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-3967626228476224836593500236546048)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1404057664633, 348186645937, 14372551297, 269869687193241, 9489435022385511, 41883631559,
    108015681389, 90380468101, 2528448705167, 2371230381051659, 90380468101, 81562861457,
    41883631559, 41883631559, 81562861457, 2528448705167, 81562861457, 67467142692597,
    108015681389, 487447389, 96677799075, 96677799075, 487447389, 604063492821,
    183838973674059, 27914730975, 6438988928818881, 8833775625, 1060053075, 27914730975,
    55476110925, 8833775625, 856169533575, 54769408875, 735356505435507, 27914730975,
    1060053075, 54769408875, 1060053075, 27914730975, 27914730975, 604063492821,
    21588579, 4281767325, 4281767325, 21588579, 43166785, 27809886915,
    295769842187, 13904985367, 43166785, 28024769113877, 46585881, 541620502930895,
    487447389, 21588579, 1083240929532805, 21588579, 42040917, 794232459,
    42040917, 487447389, 794232459, 3503099319609
  ]
def negativeCoefficients : Array ℕ := #[
    25293254300991470561627471872, 401431871717697542418451136512, 16570423466376329979989327872, 303846255670518121036863504384, 10684154007692980426964534820864, 193154158061604399565909262336,
    249067203816279357334988259328, 3334450728642433845137802002432, 5830205770964743323739419049984, 10679072260513850711389308452864, 3334450728642433845137802002432, 188071153902088494314174808064,
    193154158061604399565909262336, 193154158061604399565909262336, 188071153902088494314174808064, 5830205770964743323739419049984, 188071153902088494314174808064, 303844998690131931360355418112,
    249067203816279357334988259328, 1123977154285118059947491328, 222923827143254877629998694400, 222923827143254877629998694400, 1123977154285118059947491328, 21763680969414207084825673728,
    1655874266669333072732674326528, 257467949091138851824258252800, 14499314070235730832164533567488, 162954398158948640395100160000, 9777263889536918423706009600, 257467949091138851824258252800,
    255838405109549365420307251200, 162954398158948640395100160000, 3948385067391325556773276876800, 252579317146370392612405248000, 1655875641931909720796861300736, 257467949091138851824258252800,
    9777263889536918423706009600, 252579317146370392612405248000, 9777263889536918423706009600, 257467949091138851824258252800, 257467949091138851824258252800, 21763680969414207084825673728,
    99559747932015119529148416, 19746166506861737412447436800, 19746166506861737412447436800, 99559747932015119529148416, 796286635379844367054274560, 256500933319904527498157752320,
    2727995291772525788569425412096, 256501706413725284628611203072, 796286635379844367054274560, 7888271233650040161343373312, 107419728031911050018291712, 304905236896974919828756234240,
    1123977154285118059947491328, 99559747932015119529148416, 304905215412275644605745070080, 99559747932015119529148416, 96939754565383142699433984, 3662750726551503607940775936,
    96939754565383142699433984, 1123977154285118059947491328, 3662750726551503607940775936, 7888278395216465235680428032
  ]
def negativeScales : Array ℕ := #[
    40, 38, 33, 47, 53, 35,
    36, 36, 41, 51, 36, 36,
    35, 35, 36, 41, 36, 45,
    36, 28, 36, 36, 28, 39,
    47, 34, 52, 33, 29, 34,
    35, 33, 39, 35, 49, 34,
    29, 35, 29, 34, 34, 39,
    24, 31, 31, 24, 25, 34,
    38, 33, 25, 44, 25, 48,
    28, 24, 49, 24, 25, 29,
    25, 28, 29, 41
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    40352739326977207, 38341069915877186, 33742597128940913, 47939256273927313, 53075243618600404, 35285667486773129,
    36652449817467425, 36395291977947632, 41201389649345368, 51074557260510046, 36395291977947632, 36247193338958493,
    35285667486773129, 35285667486773129, 36247193338958493, 41201389649345368, 36247193338958493, 45939250305634612,
    36652449817467425, 28860671276030903, 36492465578579254, 36492465578579254, 28860671276030903, 39135909242257969,
    47385435977345032, 34700307601324704, 52515755592722932, 33040383042849412, 29981489371366584, 34700307601324704,
    35691147602025011, 33040383042849412, 39639105542542142, 35672651258386449, 49385437175554168, 34700307601324704,
    29981489371366584, 35672651258386449, 29981489371366584, 34700307601324704, 34700307601324704, 39135909242257969,
    24363764949854435, 31995559276577170, 31995559276577170, 24363764949854435, 25363418311162450, 34694878827117496,
    38105684001048099, 33694883175393847, 25363418311162450, 44671767720799856, 25473389441029040, 48944275690749364,
    28860671276030903, 24363764949854435, 49944275589091958, 24363764949854435, 25325290802039798, 29564986081788365,
    25325290802039798, 28860671276030903, 29564986081788365, 41671769030586421
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
noncomputable def negativeCeiling : ℝ := 19704176047 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25293254300991470561627471872, coefficient := (-25293254300991470561627471872) }, { argument := 401431871717697542418451136512, coefficient := (-401431871717697542418451136512) }, { argument := 16570423466376329979989327872, coefficient := (-16570423466376329979989327872) }, { argument := 303846255670518121036863504384, coefficient := (-303846255670518121036863504384) }, { argument := 10684154007692980426964534820864, coefficient := (-10684154007692980426964534820864) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 249067203816279357334988259328, coefficient := (-249067203816279357334988259328) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 5830205770964743323739419049984, coefficient := (-5830205770964743323739419049984) }, { argument := 10679072260513850711389308452864, coefficient := (-10679072260513850711389308452864) }, { argument := 3334450728642433845137802002432, coefficient := (-3334450728642433845137802002432) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 193154158061604399565909262336, coefficient := (-193154158061604399565909262336) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 5830205770964743323739419049984, coefficient := (-5830205770964743323739419049984) }, { argument := 188071153902088494314174808064, coefficient := (-188071153902088494314174808064) }, { argument := 303844998690131931360355418112, coefficient := (-303844998690131931360355418112) }, { argument := 249067203816279357334988259328, coefficient := (-249067203816279357334988259328) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 222923827143254877629998694400, coefficient := (-222923827143254877629998694400) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 21763680969414207084825673728, coefficient := (-21763680969414207084825673728) }, { argument := 1655874266669333072732674326528, coefficient := (-1655874266669333072732674326528) }, { argument := 257467949091138851824258252800, coefficient := (-257467949091138851824258252800) }, { argument := 14499314070235730832164533567488, coefficient := (-14499314070235730832164533567488) }, { argument := 162954398158948640395100160000, coefficient := (-162954398158948640395100160000) }, { argument := 9777263889536918423706009600, coefficient := (-9777263889536918423706009600) }, { argument := 257467949091138851824258252800, coefficient := (-257467949091138851824258252800) }, { argument := 255838405109549365420307251200, coefficient := (-255838405109549365420307251200) }, { argument := 162954398158948640395100160000, coefficient := (-162954398158948640395100160000) }, { argument := 3948385067391325556773276876800, coefficient := (-3948385067391325556773276876800) }, { argument := 252579317146370392612405248000, coefficient := (-252579317146370392612405248000) }, { argument := 1655875641931909720796861300736, coefficient := (-1655875641931909720796861300736) }, { argument := 257467949091138851824258252800, coefficient := (-257467949091138851824258252800) }, { argument := 9777263889536918423706009600, coefficient := (-9777263889536918423706009600) }, { argument := 252579317146370392612405248000, coefficient := (-252579317146370392612405248000) }, { argument := 9777263889536918423706009600, coefficient := (-9777263889536918423706009600) }, { argument := 257467949091138851824258252800, coefficient := (-257467949091138851824258252800) }, { argument := 257467949091138851824258252800, coefficient := (-257467949091138851824258252800) }, { argument := 21763680969414207084825673728, coefficient := (-21763680969414207084825673728) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 19746166506861737412447436800, coefficient := (-19746166506861737412447436800) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 256500933319904527498157752320, coefficient := (-256500933319904527498157752320) }, { argument := 2727995291772525788569425412096, coefficient := (-2727995291772525788569425412096) }, { argument := 256501706413725284628611203072, coefficient := (-256501706413725284628611203072) }, { argument := 796286635379844367054274560, coefficient := (-796286635379844367054274560) }, { argument := 7888271233650040161343373312, coefficient := (-7888271233650040161343373312) }, { argument := 107419728031911050018291712, coefficient := (-107419728031911050018291712) }, { argument := 304905236896974919828756234240, coefficient := (-304905236896974919828756234240) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 304905215412275644605745070080, coefficient := (-304905215412275644605745070080) }, { argument := 99559747932015119529148416, coefficient := (-99559747932015119529148416) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 96939754565383142699433984, coefficient := (-96939754565383142699433984) }, { argument := 1123977154285118059947491328, coefficient := (-1123977154285118059947491328) }, { argument := 3662750726551503607940775936, coefficient := (-3662750726551503607940775936) }, { argument := 7888278395216465235680428032, coefficient := (-7888278395216465235680428032) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk16
