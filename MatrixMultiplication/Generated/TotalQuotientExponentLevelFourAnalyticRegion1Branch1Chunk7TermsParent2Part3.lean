import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 3, for level-four region 1, branch 1,
parent chunk 7, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
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

namespace Parent2

namespace TermShard6

/-! Directed signed-log shard 6.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := 210418753927115451777617831372259328
def positiveArguments : Array ℕ := #[
    13793, 489, 535, 489
  ]
def positiveCoefficients : Array ℕ := #[
    2185588091118496016855503413968896, 37834542450659434651604484096, 41393620063604902941939466240, 37834542450659434651604484096
  ]
def positiveScales : Array ℕ := #[
    13, 8, 9, 8
  ]
def negativeArguments : Array ℕ := #[
    55081550143, 204614232305, 3441872221, 16773326901, 10165, 16773330891,
    10165, 1754189495, 6516376825, 109613765, 32665850067, 10165,
    32665857837, 10165, 93, 4268506725, 167047840155, 167047840155,
    4268506725, 53678198547, 199401130845, 3354181209, 32663847123, 19795,
    32663854893, 19795, 1754189495, 6516376825, 109613765, 1026672120573,
    613645, 1026672364803, 613645, 939, 32663847123, 19795,
    32663854893, 19795, 1911, 27915075966745, 5794065, 150345,
    102454147516869, 9332955, 13957214162833, 9332955, 9726165, 5794065,
    289125, 189558698889429, 1605, 189558752194347, 1605, 93,
    2648545221, 26215, 2648545851, 26215, 285, 93
  ]
def negativeCoefficients : Array ℕ := #[
    1016075258671120755354750681088, 3774466377168888237453612154880, 1015861375923156514071616946176, 77353317151853687245325205504, 192011421193479774388879360, 77353335552480900770602942464,
    192011421193479774388879360, 32359084671054801125947473920, 120205935578627013931643699200, 32352273118571863505465507840, 75322322017014626199256694784, 192011421193479774388879360,
    75322339933414807789658701824, 192011421193479774388879360, 1798881619586568211962789888, 9842506391622889596203827200, 385186094425653339530786242560, 385186094425653339530786242560,
    9842506391622889596203827200, 990187990934276914453992701952, 3678301628705986626308297195520, 989979557428299023267244539904, 75317703542594379686237700096, 186958489056809254010224640,
    75317721458994561276639707136, 186958489056809254010224640, 1035490709473753636030319165440, 3846589938516064445812598374400, 1035272739794299632174896250880, 2367344731977850747010464874496,
    5795713160761086874316963840, 2367345295133888887270938771456, 5795713160761086874316963840, 36325803027780377441571176448, 75317703542594379686237700096, 186958489056809254010224640,
    75317721458994561276639707136, 186958489056809254010224640, 36964115860536901645816037376, 62859162860925935194745077760, 213763268402875866367918080, 11093502951047450150830080,
    230706230289766528223136448512, 344325264672895856604610560, 62857704502864908081763975168, 344325264672895856604610560, 358832153147342522186465280, 213763268402875866367918080,
    10666829760622548221952000, 106712060710408562293340110848, 242540742560184978175426560, 106712090718409667520195723264, 242540742560184978175426560, 1798881619586568211962789888,
    97714071718867009349219254272, 247593674696855498554081280, 97714094961764542223254290432, 247593674696855498554081280, 44101613899541672293281300480, 1798881619586568211962789888
  ]
def negativeScales : Array ℕ := #[
    35, 37, 31, 33, 13, 33,
    13, 30, 32, 26, 34, 13,
    34, 13, 6, 31, 37, 37,
    31, 35, 37, 31, 34, 14,
    34, 14, 30, 32, 26, 39,
    19, 39, 19, 9, 34, 14,
    34, 14, 10, 44, 22, 17,
    46, 23, 43, 23, 23, 22,
    18, 47, 10, 47, 10, 6,
    31, 14, 31, 14, 8, 6
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    13751648659041397, 8933690654464738, 9063395081288509, 8933690654464738
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    35680850110283206, 37574115541543558, 31680546392562833, 33965449830616296, 13311322594732096, 33965450173801274,
    13311322594732096, 30708157456320712, 32601422887542458, 26707853738600059, 34927064139552001, 13311322594732096,
    34927064482715901, 13311322594732096, 6539158811108986, 31991084326739097, 37281470373229352, 37281470373229352,
    31991084326739097, 35643617204056500, 37536882635342755, 31643313486336323, 34926975676330714, 14272848446917460,
    34926976019515657, 14272848446917460, 30708157456320712, 32601422887542458, 26707853738600059, 39901112657234143,
    19227044757304335, 39901113000429784, 19227044757304335, 9874981350423323, 34926975676330714, 14272848446917460,
    34926976019515657, 14272848446917460, 10900112067353854, 44666109715772095, 22466144438718846, 17197917363664646,
    46541971716686442, 23153902508801334, 43666076244273984, 23153902508801334, 23213439635778698, 22466144438718846,
    18141333835298278, 47429637992036260, 10648357582030099, 47429638397729750, 10648357582030099, 6539158811108986,
    31302552995264751, 14678104925446590, 31302553338433431, 14678104925446590, 8154818109052105, 6539158811108986
  ]

abbrev PositiveTerm := Fin 4
abbrev NegativeTerm := Fin 60
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
noncomputable def positiveFloor : ℝ := 904479617 / 2500000000
noncomputable def negativeCeiling : ℝ := 10578966513 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1016075258671120755354750681088, coefficient := (-1016075258671120755354750681088) }, { argument := 3774466377168888237453612154880, coefficient := (-3774466377168888237453612154880) }, { argument := 1015861375923156514071616946176, coefficient := (-1015861375923156514071616946176) }, { argument := 77353317151853687245325205504, coefficient := (-77353317151853687245325205504) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 77353335552480900770602942464, coefficient := (-77353335552480900770602942464) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 32359084671054801125947473920, coefficient := (-32359084671054801125947473920) }, { argument := 120205935578627013931643699200, coefficient := (-120205935578627013931643699200) }, { argument := 32352273118571863505465507840, coefficient := (-32352273118571863505465507840) }, { argument := 75322322017014626199256694784, coefficient := (-75322322017014626199256694784) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 75322339933414807789658701824, coefficient := (-75322339933414807789658701824) }, { argument := 192011421193479774388879360, coefficient := (-192011421193479774388879360) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 385186094425653339530786242560, coefficient := (-385186094425653339530786242560) }, { argument := 9842506391622889596203827200, coefficient := (-9842506391622889596203827200) }, { argument := 990187990934276914453992701952, coefficient := (-990187990934276914453992701952) }, { argument := 3678301628705986626308297195520, coefficient := (-3678301628705986626308297195520) }, { argument := 989979557428299023267244539904, coefficient := (-989979557428299023267244539904) }, { argument := 75317703542594379686237700096, coefficient := (-75317703542594379686237700096) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 75317721458994561276639707136, coefficient := (-75317721458994561276639707136) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 1035490709473753636030319165440, coefficient := (-1035490709473753636030319165440) }, { argument := 3846589938516064445812598374400, coefficient := (-3846589938516064445812598374400) }, { argument := 1035272739794299632174896250880, coefficient := (-1035272739794299632174896250880) }, { argument := 2367344731977850747010464874496, coefficient := (-2367344731977850747010464874496) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 2367345295133888887270938771456, coefficient := (-2367345295133888887270938771456) }, { argument := 5795713160761086874316963840, coefficient := (-5795713160761086874316963840) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 75317703542594379686237700096, coefficient := (-75317703542594379686237700096) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 75317721458994561276639707136, coefficient := (-75317721458994561276639707136) }, { argument := 186958489056809254010224640, coefficient := (-186958489056809254010224640) }, { argument := 36964115860536901645816037376, coefficient := (-36964115860536901645816037376) }, { argument := 62859162860925935194745077760, coefficient := (-62859162860925935194745077760) }, { argument := 213763268402875866367918080, coefficient := (-213763268402875866367918080) }, { argument := 11093502951047450150830080, coefficient := (-11093502951047450150830080) }, { argument := 230706230289766528223136448512, coefficient := (-230706230289766528223136448512) }, { argument := 344325264672895856604610560, coefficient := (-344325264672895856604610560) }, { argument := 62857704502864908081763975168, coefficient := (-62857704502864908081763975168) }, { argument := 344325264672895856604610560, coefficient := (-344325264672895856604610560) }, { argument := 358832153147342522186465280, coefficient := (-358832153147342522186465280) }, { argument := 213763268402875866367918080, coefficient := (-213763268402875866367918080) }, { argument := 10666829760622548221952000, coefficient := (-10666829760622548221952000) }, { argument := 106712060710408562293340110848, coefficient := (-106712060710408562293340110848) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 106712090718409667520195723264, coefficient := (-106712090718409667520195723264) }, { argument := 242540742560184978175426560, coefficient := (-242540742560184978175426560) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 97714071718867009349219254272, coefficient := (-97714071718867009349219254272) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 97714094961764542223254290432, coefficient := (-97714094961764542223254290432) }, { argument := 247593674696855498554081280, coefficient := (-247593674696855498554081280) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 2185588091118496016855503413968896, coefficient := 2185588091118496016855503413968896 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }, { argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 37834542450659434651604484096, coefficient := 37834542450659434651604484096 }] }

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


end Parent2

namespace Parent2

namespace TermShard7

/-! Directed signed-log shard 7.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2832228778633050340218412294209536)
def positiveArguments : Array ℕ := #[
    535, 177, 29559, 767, 31801, 47613,
    1475, 47613, 49619, 29559, 1475, 71641,
    80885, 34665, 912845, 80885, 34665, 80885,
    80885, 3353261, 20799, 912845, 3353261, 71641,
    80885, 20799, 80885, 11505, 333645, 295295,
    19175, 11505, 19175, 586755, 19175, 11505,
    9399585, 602095, 333645, 586755, 19175, 602095,
    19175, 586755, 19175, 11505, 611, 455,
    481, 39, 8359, 15119, 455, 8359,
    247, 247, 481, 481, 15119, 481
  ]
def positiveCoefficients : Array ℕ := #[
    41393620063604902941939466240, 27389423369189038582143123456, 571754212831821180402237702144, 29671875316621458463988383744, 615120799833037158157297647616, 920969360788981422324562526208,
    28530649342905248523065753600, 920969360788981422324562526208, 959771043895332560315931951104, 571754212831821180402237702144, 28530649342905248523065753600, 1385738474288186379282002477056,
    1564543438712468492737744732160, 1341037233182115850918066913280, 17656990236897858703754547691520, 1564543438712468492737744732160, 1341037233182115850918066913280, 1564543438712468492737744732160,
    1564543438712468492737744732160, 64861500844908336656070503038976, 1609244679818539021101680295936, 17656990236897858703754547691520, 64861500844908336656070503038976, 1385738474288186379282002477056,
    1564543438712468492737744732160, 1609244679818539021101680295936, 1564543438712468492737744732160, 445078129749321876959825756160, 6453632881365167215917473464320, 11423671996899261508635527741440,
    370898441457768230799854796800, 7121250075989150031357212098560, 370898441457768230799854796800, 11349492308607707862475556782080, 11868750126648583385595353497600, 7121250075989150031357212098560,
    181814416002597986738088821391360, 11646211061773922447115440619520, 6453632881365167215917473464320, 11349492308607707862475556782080, 370898441457768230799854796800, 11646211061773922447115440619520,
    370898441457768230799854796800, 11349492308607707862475556782080, 11868750126648583385595353497600, 445078129749321876959825756160, 378190682001683673981682450432, 281631358937424012539550760960,
    297724579448133956113239375872, 386237292257038645768526757888, 5173970394193246858940889694208, 9358207726977832188099929571328, 281631358937424012539550760960, 5173970394193246858940889694208,
    305771189703488927900083683328, 305771189703488927900083683328, 297724579448133956113239375872, 297724579448133956113239375872, 9358207726977832188099929571328, 297724579448133956113239375872
  ]
def positiveScales : Array ℕ := #[
    9, 7, 14, 9, 14, 15,
    10, 15, 15, 14, 10, 16,
    16, 15, 19, 16, 15, 16,
    16, 21, 14, 19, 21, 16,
    16, 14, 16, 13, 18, 18,
    14, 13, 14, 19, 14, 13,
    23, 19, 18, 19, 14, 19,
    14, 19, 14, 13, 9, 8,
    8, 5, 13, 13, 8, 13,
    7, 7, 8, 8, 13, 8
  ]
def negativeArguments : Array ℕ := #[
    1, 59, 2311, 3835
  ]
def negativeCoefficients : Array ℕ := #[
    158456325028528675187087900672, 4674461588341595918019093069824, 183096283570464884178680069226496, 303840003242203734671241049538560
  ]
def negativeScales : Array ℕ := #[
    0, 5, 11, 11
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    9063395081288509, 7467605550082991, 14851309842447145, 9583082767502714, 14956784511393203, 15539067912639561,
    10526499239136525, 15539067912639561, 15598605039616646, 14851309842447145, 10526499239136525, 16128497854854506,
    16303584561412597, 15081192140076149, 19800010387492060, 16303584561412597, 15081192140076149, 16303584561412597,
    16303584561412597, 21677133348531774, 14344226545909942, 19800010387492060, 21677133348531774, 16128497854854506,
    16303584561412597, 14344226545909942, 16303584561412597, 13489973363111439, 18347954358239023, 18171797403085196,
    14226938957277657, 13489973363111439, 14226938957277657, 19162398705082947, 14226938957277657, 13489973363111439,
    23164165631257135, 19199631611281922, 18347954358239023, 19162398705082947, 14226938957277657, 19199631611281922,
    14226938957277657, 19162398705082947, 14226938957277657, 13489973363111439, 9255028569818729, 8829722735013603,
    8909893083448106, 5285402218862248, 13029114645469039, 13884075099411883, 8829722735013603, 13029114645469039,
    7948367230958674, 7948367230958674, 8909893083448106, 8909893083448106, 13884075099411883, 8909893083448106
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    0, 5882643052550791, 11174301544467632, 11905010867167127
  ]

abbrev PositiveTerm := Fin 60
abbrev NegativeTerm := Fin 4
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
noncomputable def positiveFloor : ℝ := 127666495943 / 1000000000000
noncomputable def negativeCeiling : ℝ := 68499186979 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 41393620063604902941939466240, coefficient := 41393620063604902941939466240 }, { argument := 158456325028528675187087900672, coefficient := (-158456325028528675187087900672) }, { argument := 27389423369189038582143123456, coefficient := 27389423369189038582143123456 }, { argument := 571754212831821180402237702144, coefficient := 571754212831821180402237702144 }, { argument := 29671875316621458463988383744, coefficient := 29671875316621458463988383744 }, { argument := 615120799833037158157297647616, coefficient := 615120799833037158157297647616 }, { argument := 920969360788981422324562526208, coefficient := 920969360788981422324562526208 }, { argument := 28530649342905248523065753600, coefficient := 28530649342905248523065753600 }, { argument := 920969360788981422324562526208, coefficient := 920969360788981422324562526208 }, { argument := 959771043895332560315931951104, coefficient := 959771043895332560315931951104 }, { argument := 571754212831821180402237702144, coefficient := 571754212831821180402237702144 }, { argument := 28530649342905248523065753600, coefficient := 28530649342905248523065753600 }, { argument := 4674461588341595918019093069824, coefficient := (-4674461588341595918019093069824) }, { argument := 1385738474288186379282002477056, coefficient := 1385738474288186379282002477056 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1341037233182115850918066913280, coefficient := 1341037233182115850918066913280 }, { argument := 17656990236897858703754547691520, coefficient := 17656990236897858703754547691520 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1341037233182115850918066913280, coefficient := 1341037233182115850918066913280 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 64861500844908336656070503038976, coefficient := 64861500844908336656070503038976 }, { argument := 1609244679818539021101680295936, coefficient := 1609244679818539021101680295936 }, { argument := 17656990236897858703754547691520, coefficient := 17656990236897858703754547691520 }, { argument := 64861500844908336656070503038976, coefficient := 64861500844908336656070503038976 }, { argument := 1385738474288186379282002477056, coefficient := 1385738474288186379282002477056 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 1609244679818539021101680295936, coefficient := 1609244679818539021101680295936 }, { argument := 1564543438712468492737744732160, coefficient := 1564543438712468492737744732160 }, { argument := 183096283570464884178680069226496, coefficient := (-183096283570464884178680069226496) }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 6453632881365167215917473464320, coefficient := 6453632881365167215917473464320 }, { argument := 11423671996899261508635527741440, coefficient := 11423671996899261508635527741440 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 7121250075989150031357212098560, coefficient := 7121250075989150031357212098560 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }, { argument := 11868750126648583385595353497600, coefficient := 11868750126648583385595353497600 }, { argument := 7121250075989150031357212098560, coefficient := 7121250075989150031357212098560 }, { argument := 181814416002597986738088821391360, coefficient := 181814416002597986738088821391360 }, { argument := 11646211061773922447115440619520, coefficient := 11646211061773922447115440619520 }, { argument := 6453632881365167215917473464320, coefficient := 6453632881365167215917473464320 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 11646211061773922447115440619520, coefficient := 11646211061773922447115440619520 }, { argument := 370898441457768230799854796800, coefficient := 370898441457768230799854796800 }, { argument := 11349492308607707862475556782080, coefficient := 11349492308607707862475556782080 }, { argument := 11868750126648583385595353497600, coefficient := 11868750126648583385595353497600 }, { argument := 445078129749321876959825756160, coefficient := 445078129749321876959825756160 }, { argument := 303840003242203734671241049538560, coefficient := (-303840003242203734671241049538560) }, { argument := 378190682001683673981682450432, coefficient := 378190682001683673981682450432 }, { argument := 281631358937424012539550760960, coefficient := 281631358937424012539550760960 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }, { argument := 386237292257038645768526757888, coefficient := 386237292257038645768526757888 }, { argument := 5173970394193246858940889694208, coefficient := 5173970394193246858940889694208 }, { argument := 9358207726977832188099929571328, coefficient := 9358207726977832188099929571328 }, { argument := 281631358937424012539550760960, coefficient := 281631358937424012539550760960 }, { argument := 5173970394193246858940889694208, coefficient := 5173970394193246858940889694208 }, { argument := 305771189703488927900083683328, coefficient := 305771189703488927900083683328 }, { argument := 305771189703488927900083683328, coefficient := 305771189703488927900083683328 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }, { argument := 9358207726977832188099929571328, coefficient := 9358207726977832188099929571328 }, { argument := 297724579448133956113239375872, coefficient := 297724579448133956113239375872 }] }

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


end Parent2

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk7
