import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 19, parent 1; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent1

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-59008286337583776155653817323487232)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    289768441, 123, 11192532193, 1287, 57, 11192531021,
    57, 111, 2097, 111, 1287, 2097,
    289769177, 111, 111, 123, 4382192788522147, 2055208225,
    1702886815, 509853513995555819, 11450445825, 140222446647216053, 45860503535, 45860503535,
    32824611365, 1702886815, 140106814512124535, 49801569, 140106806723390857, 49801569,
    49801569, 362830393, 99603205, 2055208225, 2055209695, 72338119,
    1702886815, 1702888033, 123, 4382192545856349, 2055209695, 1702888033,
    509853487415913493, 11450454015, 140222438879950923, 45860536337, 45860536337, 32824634843,
    1702888033, 509396508002165095, 362830393, 509396481335156377, 362830393, 11176170957,
    11450445825, 11450454015, 1287, 57, 70049559993261585, 99603205,
    70049556097917423, 99603205, 2794042441, 57
  ]
def negativeCoefficients : Array ℕ := #[
    1368392773571790299795801767936, 19033328104012721726574034944, 52855238886662687076780844515328, 199153603820035551724396609536, 17640645559816668917312520192, 52855233352049169153556654063616,
    17640645559816668917312520192, 17176418045084651314225348608, 648990065595360609115865874432, 17176418045084651314225348608, 199153603820035551724396609536, 648990065595360609115865874432,
    1368396249233521691854679048192, 17176418045084651314225348608, 17176418045084651314225348608, 19033328104012721726574034944, 39471283618908032019630940749824, 37911900144757876742265241600,
    1963294828924961474153021440, 143511005977745197101711060107264, 52805860915912756891012300800, 39469109904336342029513699360768, 52873560737599824528052060160, 52873560737599824528052060160,
    37844200323070809105225482240, 1963294828924961474153021440, 39436562351804453572064533544960, 3674707191248749283053142016, 39436560159470822951512484872192, 3674707191248749283053142016,
    3674707191248749283053142016, 13386078803668915161374130176, 3674709663112455160133058560, 37911900144757876742265241600, 37911927261471665095306117120, 1366428434397743427824486711296,
    1963294828924961474153021440, 1963296233183354085292638208, 19033328104012721726574034944, 39471281433168837122902833758208, 37911927261471665095306117120, 1963296233183354085292638208,
    143510998496240992413294587281408, 52805898685621247811319234560, 39469107718045570457273251135488, 52873598555731018641846566912, 52873598555731018641846566912, 37844227391361894264778784768,
    1963296233183354085292638208, 143382370226398912853949357752320, 13386078803668915161374130176, 143382362720303255012038842253312, 13386078803668915161374130176, 52777975134157966854203293827072,
    52805860915912756891012300800, 52805898685621247811319234560, 199153603820035551724396609536, 17640645559816668917312520192, 39434396535390009812336529899520, 3674709663112455160133058560,
    39434394342506195254456904318976, 3674709663112455160133058560, 52777969500374752790716553887744, 17640645559816668917312520192
  ]
def negativeScales : Array ℕ := #[
    28, 6, 33, 10, 5, 33,
    5, 6, 11, 6, 10, 11,
    28, 6, 6, 6, 51, 30,
    30, 58, 33, 56, 35, 35,
    34, 30, 56, 25, 56, 25,
    25, 28, 26, 30, 30, 26,
    30, 30, 6, 51, 30, 30,
    58, 33, 56, 35, 35, 34,
    30, 58, 28, 58, 28, 33,
    33, 33, 10, 5, 55, 26,
    55, 26, 31, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    28110325237043889, 6942514514520450, 33381817416734442, 10329796338220703, 5832890015409720, 33381817265665975,
    5832890015409720, 6794415866926375, 11034111146096593, 6794415866926375, 10329796338220703, 11034111146096593,
    28110328901425690, 6794415866926375, 6794415866926375, 6942514514520450, 51960574390859623, 30936637431358162,
    30665335401268456, 58822860420037633, 33414684719859182, 56960494938307022, 35416533144251552, 35416533144251552,
    34934058886896563, 30665335401268456, 56959304752516848, 25569687859375988, 56959304672315396, 25569687859375988,
    25569687859375988, 28434720069413648, 26569688829832714, 30936637431358162, 30936638463254214, 26108252748455518,
    30665335401268456, 30665336433164362, 6942514514520450, 51960574310969750, 30936638463254214, 30665336433164362,
    58822860344827168, 33414685751755088, 56960494858392587, 35416534176147457, 35416534176147457, 34934059918792610,
    30665336433164362, 58821566683813064, 28434720069413648, 58821566608287687, 28434720069413648, 33379706943177604,
    33414684719859182, 33414685751755088, 10329796338220703, 5832890015409720, 55959225518961655, 26569688829832714,
    55959225438735670, 26569688829832714, 31379706789177161, 5832890015409720
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
noncomputable def negativeCeiling : ℝ := 175622775483 / 250000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1368392773571790299795801767936, coefficient := (-1368392773571790299795801767936) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 52855238886662687076780844515328, coefficient := (-52855238886662687076780844515328) }, { argument := 199153603820035551724396609536, coefficient := (-199153603820035551724396609536) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }, { argument := 52855233352049169153556654063616, coefficient := (-52855233352049169153556654063616) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 648990065595360609115865874432, coefficient := (-648990065595360609115865874432) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 199153603820035551724396609536, coefficient := (-199153603820035551724396609536) }, { argument := 648990065595360609115865874432, coefficient := (-648990065595360609115865874432) }, { argument := 1368396249233521691854679048192, coefficient := (-1368396249233521691854679048192) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 39471283618908032019630940749824, coefficient := (-39471283618908032019630940749824) }, { argument := 37911900144757876742265241600, coefficient := (-37911900144757876742265241600) }, { argument := 1963294828924961474153021440, coefficient := (-1963294828924961474153021440) }, { argument := 143511005977745197101711060107264, coefficient := (-143511005977745197101711060107264) }, { argument := 52805860915912756891012300800, coefficient := (-52805860915912756891012300800) }, { argument := 39469109904336342029513699360768, coefficient := (-39469109904336342029513699360768) }, { argument := 52873560737599824528052060160, coefficient := (-52873560737599824528052060160) }, { argument := 52873560737599824528052060160, coefficient := (-52873560737599824528052060160) }, { argument := 37844200323070809105225482240, coefficient := (-37844200323070809105225482240) }, { argument := 1963294828924961474153021440, coefficient := (-1963294828924961474153021440) }, { argument := 39436562351804453572064533544960, coefficient := (-39436562351804453572064533544960) }, { argument := 3674707191248749283053142016, coefficient := (-3674707191248749283053142016) }, { argument := 39436560159470822951512484872192, coefficient := (-39436560159470822951512484872192) }, { argument := 3674707191248749283053142016, coefficient := (-3674707191248749283053142016) }, { argument := 3674707191248749283053142016, coefficient := (-3674707191248749283053142016) }, { argument := 13386078803668915161374130176, coefficient := (-13386078803668915161374130176) }, { argument := 3674709663112455160133058560, coefficient := (-3674709663112455160133058560) }, { argument := 37911900144757876742265241600, coefficient := (-37911900144757876742265241600) }, { argument := 37911927261471665095306117120, coefficient := (-37911927261471665095306117120) }, { argument := 1366428434397743427824486711296, coefficient := (-1366428434397743427824486711296) }, { argument := 1963294828924961474153021440, coefficient := (-1963294828924961474153021440) }, { argument := 1963296233183354085292638208, coefficient := (-1963296233183354085292638208) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 39471281433168837122902833758208, coefficient := (-39471281433168837122902833758208) }, { argument := 37911927261471665095306117120, coefficient := (-37911927261471665095306117120) }, { argument := 1963296233183354085292638208, coefficient := (-1963296233183354085292638208) }, { argument := 143510998496240992413294587281408, coefficient := (-143510998496240992413294587281408) }, { argument := 52805898685621247811319234560, coefficient := (-52805898685621247811319234560) }, { argument := 39469107718045570457273251135488, coefficient := (-39469107718045570457273251135488) }, { argument := 52873598555731018641846566912, coefficient := (-52873598555731018641846566912) }, { argument := 52873598555731018641846566912, coefficient := (-52873598555731018641846566912) }, { argument := 37844227391361894264778784768, coefficient := (-37844227391361894264778784768) }, { argument := 1963296233183354085292638208, coefficient := (-1963296233183354085292638208) }, { argument := 143382370226398912853949357752320, coefficient := (-143382370226398912853949357752320) }, { argument := 13386078803668915161374130176, coefficient := (-13386078803668915161374130176) }, { argument := 143382362720303255012038842253312, coefficient := (-143382362720303255012038842253312) }, { argument := 13386078803668915161374130176, coefficient := (-13386078803668915161374130176) }, { argument := 52777975134157966854203293827072, coefficient := (-52777975134157966854203293827072) }, { argument := 52805860915912756891012300800, coefficient := (-52805860915912756891012300800) }, { argument := 52805898685621247811319234560, coefficient := (-52805898685621247811319234560) }, { argument := 199153603820035551724396609536, coefficient := (-199153603820035551724396609536) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }, { argument := 39434396535390009812336529899520, coefficient := (-39434396535390009812336529899520) }, { argument := 3674709663112455160133058560, coefficient := (-3674709663112455160133058560) }, { argument := 39434394342506195254456904318976, coefficient := (-39434394342506195254456904318976) }, { argument := 3674709663112455160133058560, coefficient := (-3674709663112455160133058560) }, { argument := 52777969500374752790716553887744, coefficient := (-52777969500374752790716553887744) }, { argument := 17640645559816668917312520192, coefficient := (-17640645559816668917312520192) }] }

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
def constantNumerator : ℤ := 64861593203953154322488367704440832
def positiveArguments : Array ℕ := #[
    14021, 27, 123, 3, 1287, 57,
    3, 57, 111, 2097, 111, 1287,
    2097, 27, 111, 111, 123, 49,
    245, 203, 3647, 1365, 49, 5467,
    5467, 3913, 203, 61, 67, 61,
    67, 1391, 47131395287, 47131392809, 16710139353, 121485530049,
    33418440845, 572043029
  ]
def positiveCoefficients : Array ℕ := #[
    1110858066612500277399079727661056, 33424381060705267422276354048, 38066656208025443453148069888, 29710560942849126597578981376, 398307207640071103448793219072, 35281291119633337834625040384,
    29710560942849126597578981376, 35281291119633337834625040384, 34352836090169302628450697216, 1297980131190721218231731748864, 34352836090169302628450697216, 398307207640071103448793219072,
    1297980131190721218231731748864, 33424381060705267422276354048, 34352836090169302628450697216, 34352836090169302628450697216, 38066656208025443453148069888, 7582382740622954183757135872,
    151647654812459083675142717440, 7853182124216631118891319296, 141086478852305683204909563904, 211223519203068009404663070720, 7582382740622954183757135872, 211494318586661686339797254144,
    211494318586661686339797254144, 151376855428865406740008534016, 7853182124216631118891319296, 37757171198204098384423288832, 41470991316060239209120661504, 37757171198204098384423288832,
    41470991316060239209120661504, 220412748114683387185239269834752, 445143442788418325320307524501504, 445143419384370036218345845424128, 157822804009376517709059248357376, 573699195257050727358434434351104,
    157814124956189944420037159813120, 2701396826908828460198012125184
  ]
def positiveScales : Array ℕ := #[
    13, 4, 6, 1, 10, 5,
    1, 5, 6, 11, 6, 10,
    11, 4, 6, 6, 6, 5,
    7, 7, 11, 10, 5, 12,
    12, 11, 7, 5, 6, 5,
    6, 10, 35, 35, 33, 36,
    34, 29
  ]
def negativeArguments : Array ℕ := #[
    49801569, 362830393, 99603205, 45860503535, 45860536337, 111,
    45860503535, 45860536337, 2097, 111, 32824611365, 32824634843,
    1287, 2097, 289353203, 1702886815, 1702888033, 111,
    111, 123, 3, 7, 1, 1391,
    11237, 11225
  ]
def negativeCoefficients : Array ℕ := #[
    3674707191248749283053142016, 13386078803668915161374130176, 3674709663112455160133058560, 52873560737599824528052060160, 52873598555731018641846566912, 17176418045084651314225348608,
    52873560737599824528052060160, 52873598555731018641846566912, 648990065595360609115865874432, 17176418045084651314225348608, 37844200323070809105225482240, 37844227391361894264778784768,
    199153603820035551724396609536, 648990065595360609115865874432, 1366431867558176474056557068288, 1963294828924961474153021440, 1963296233183354085292638208, 17176418045084651314225348608,
    17176418045084651314225348608, 19033328104012721726574034944, 3802951800684688204490109616128, 1109194275199700726309615304704, 158456325028528675187087900672, 220412748114683387185239269834752,
    890286862172788361538653369925632, 889336124222617189487530842521600
  ]
def negativeScales : Array ℕ := #[
    25, 28, 26, 35, 35, 6,
    35, 35, 11, 6, 34, 34,
    10, 11, 28, 30, 30, 6,
    6, 6, 1, 2, 0, 10,
    13, 13
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13775301627846313, 4754887502147955, 6942514504772358, 1584962500720924, 10329796338220701, 5832890014087662,
    1584962500720924, 5832890014087662, 6794415866314396, 11034111146096592, 6794415866314396, 10329796338220701,
    11034111146096592, 4754887502147955, 6794415866314396, 6794415866314396, 6942514504772358, 5614709844114682,
    7936637938489789, 7665335917183229, 11832494484259625, 10414685235807213, 5614709844114682, 12416533660199582,
    12416533660199582, 11934059394410200, 7665335917183229, 5930737337099561, 6066089190457772, 5930737337099561,
    6066089190457772, 10441906704542236, 35455969340683897, 35455969264832155, 33960004712812992, 36821993530618386,
    34959925373384128, 29091548429511858
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    25569687859375988, 28434720069413648, 26569688829832714, 35416533144251552, 35416534176147457, 6794415866926375,
    35416533144251552, 35416534176147457, 11034111146096593, 6794415866926375, 34934058886896563, 34934059918792610,
    10329796338220703, 11034111146096593, 28108256373231748, 30665335401268456, 30665336433164362, 6794415866926375,
    6794415866926375, 6942514514520450, 1584962500724866, 2807354922807594, 0, 10441906704542274,
    13455969302758090, 13454427824515927
  ]

abbrev PositiveTerm := Fin 38
abbrev NegativeTerm := Fin 26
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
noncomputable def positiveFloor : ℝ := 978643651629 / 1000000000000
noncomputable def negativeCeiling : ℝ := 158420169529 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 3674707191248749283053142016, coefficient := (-3674707191248749283053142016) }, { argument := 13386078803668915161374130176, coefficient := (-13386078803668915161374130176) }, { argument := 3674709663112455160133058560, coefficient := (-3674709663112455160133058560) }, { argument := 52873560737599824528052060160, coefficient := (-52873560737599824528052060160) }, { argument := 52873598555731018641846566912, coefficient := (-52873598555731018641846566912) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 52873560737599824528052060160, coefficient := (-52873560737599824528052060160) }, { argument := 52873598555731018641846566912, coefficient := (-52873598555731018641846566912) }, { argument := 648990065595360609115865874432, coefficient := (-648990065595360609115865874432) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 37844200323070809105225482240, coefficient := (-37844200323070809105225482240) }, { argument := 37844227391361894264778784768, coefficient := (-37844227391361894264778784768) }, { argument := 199153603820035551724396609536, coefficient := (-199153603820035551724396609536) }, { argument := 648990065595360609115865874432, coefficient := (-648990065595360609115865874432) }, { argument := 1366431867558176474056557068288, coefficient := (-1366431867558176474056557068288) }, { argument := 1963294828924961474153021440, coefficient := (-1963294828924961474153021440) }, { argument := 1963296233183354085292638208, coefficient := (-1963296233183354085292638208) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 17176418045084651314225348608, coefficient := (-17176418045084651314225348608) }, { argument := 19033328104012721726574034944, coefficient := (-19033328104012721726574034944) }, { argument := 1110858066612500277399079727661056, coefficient := 1110858066612500277399079727661056 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 38066656208025443453148069888, coefficient := 38066656208025443453148069888 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 398307207640071103448793219072, coefficient := 398307207640071103448793219072 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 29710560942849126597578981376, coefficient := 29710560942849126597578981376 }, { argument := 35281291119633337834625040384, coefficient := 35281291119633337834625040384 }, { argument := 34352836090169302628450697216, coefficient := 34352836090169302628450697216 }, { argument := 1297980131190721218231731748864, coefficient := 1297980131190721218231731748864 }, { argument := 34352836090169302628450697216, coefficient := 34352836090169302628450697216 }, { argument := 398307207640071103448793219072, coefficient := 398307207640071103448793219072 }, { argument := 1297980131190721218231731748864, coefficient := 1297980131190721218231731748864 }, { argument := 33424381060705267422276354048, coefficient := 33424381060705267422276354048 }, { argument := 34352836090169302628450697216, coefficient := 34352836090169302628450697216 }, { argument := 34352836090169302628450697216, coefficient := 34352836090169302628450697216 }, { argument := 38066656208025443453148069888, coefficient := 38066656208025443453148069888 }, { argument := 3802951800684688204490109616128, coefficient := (-3802951800684688204490109616128) }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 151647654812459083675142717440, coefficient := 151647654812459083675142717440 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 141086478852305683204909563904, coefficient := 141086478852305683204909563904 }, { argument := 211223519203068009404663070720, coefficient := 211223519203068009404663070720 }, { argument := 7582382740622954183757135872, coefficient := 7582382740622954183757135872 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 211494318586661686339797254144, coefficient := 211494318586661686339797254144 }, { argument := 151376855428865406740008534016, coefficient := 151376855428865406740008534016 }, { argument := 7853182124216631118891319296, coefficient := 7853182124216631118891319296 }, { argument := 1109194275199700726309615304704, coefficient := (-1109194275199700726309615304704) }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 37757171198204098384423288832, coefficient := 37757171198204098384423288832 }, { argument := 41470991316060239209120661504, coefficient := 41470991316060239209120661504 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 220412748114683387185239269834752, coefficient := 220412748114683387185239269834752 }, { argument := 220412748114683387185239269834752, coefficient := (-220412748114683387185239269834752) }, { argument := 445143442788418325320307524501504, coefficient := 445143442788418325320307524501504 }, { argument := 445143419384370036218345845424128, coefficient := 445143419384370036218345845424128 }, { argument := 890286862172788361538653369925632, coefficient := (-890286862172788361538653369925632) }, { argument := 157822804009376517709059248357376, coefficient := 157822804009376517709059248357376 }, { argument := 573699195257050727358434434351104, coefficient := 573699195257050727358434434351104 }, { argument := 157814124956189944420037159813120, coefficient := 157814124956189944420037159813120 }, { argument := 889336124222617189487530842521600, coefficient := (-889336124222617189487530842521600) }, { argument := 2701396826908828460198012125184, coefficient := 2701396826908828460198012125184 }] }

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

namespace Parent1

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-5498739168456063333051621399592960)
def positiveArguments : Array ℕ := #[
    11181205847, 22362409329, 143011123
  ]
def positiveCoefficients : Array ℕ := #[
    105603503459877804804386559361024, 105603492291481072817675628969984, 2701403735730992898488959762432
  ]
def positiveScales : Array ℕ := #[
    33, 34, 27
  ]
def negativeArguments : Array ℕ := #[
    1367
  ]
def negativeCoefficients : Array ℕ := #[
    216609796313998698980749160218624
  ]
def negativeScales : Array ℕ := #[
    10
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    33380356734163447, 34380356581587150, 27091552119199589
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    10416797527606073
  ]

abbrev PositiveTerm := Fin 3
abbrev NegativeTerm := Fin 1
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
noncomputable def positiveFloor : ℝ := 87015363289 / 1000000000000
noncomputable def negativeCeiling : ℝ := 27160191003 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 105603503459877804804386559361024, coefficient := 105603503459877804804386559361024 }, { argument := 105603492291481072817675628969984, coefficient := 105603492291481072817675628969984 }, { argument := 2701403735730992898488959762432, coefficient := 2701403735730992898488959762432 }, { argument := 216609796313998698980749160218624, coefficient := (-216609796313998698980749160218624) }] }

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


end Parent1

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk19
