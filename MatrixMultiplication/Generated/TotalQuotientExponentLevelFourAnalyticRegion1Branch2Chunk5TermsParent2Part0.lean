import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 2,
parent chunk 5, parent 2; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5

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
def constantNumerator : ℤ := (-363161134056004878725362541920256)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3782293, 141, 57351347, 3489, 111, 114702741,
    57, 57, 1929, 105, 3489, 1929,
    236391, 111, 105, 141, 4776344742507, 285,
    93, 143993680781497, 939, 38210749549551, 1881, 843,
    285, 93, 4776344742507, 2772737289, 4774876483477, 1399987197,
    2772737289, 4699415287, 2772737289, 285, 285, 3782293,
    93, 93, 141, 4774876483477, 285, 93,
    143953520164679, 939, 38199003481105, 1881, 843, 285,
    93, 143993680781497, 4699415287, 143953520164679, 2372789251, 57351347,
    939, 939, 3489, 111, 38210749549551, 2772737289,
    38199003481105, 1399987197, 114702741, 57
  ]
def negativeCoefficients : Array ℕ := #[
    17861373691592479004245884928, 2727336649050603418137133056, 541668157640453156835136897024, 67487074954167059048797569024, 2147052255635581414278168576, 541668379591677851708461940736,
    2205080694977083614664065024, 2205080694977083614664065024, 37312286496585914848131416064, 2030995376952577013506375680, 67487074954167059048797569024, 37312286496585914848131416064,
    17861198964032612827372978176, 2147052255635581414278168576, 2030995376952577013506375680, 2727336649050603418137133056, 86042977610190211466435493888, 44101613899541672293281300480,
    1798881619586568211962789888, 324244943555628020228220256256, 36325803027780377441571176448, 86042958716452615741293723648, 36383831467121879641957072896, 32611982909924236616873803776,
    44101613899541672293281300480, 1798881619586568211962789888, 86042977610190211466435493888, 25573987576907119160576704512, 86016527806908646002805178368, 25825205529528996559010660352,
    25573987576907119160576704512, 86688911095367321662145953792, 25573987576907119160576704512, 44101613899541672293281300480, 44101613899541672293281300480, 17861373691592479004245884928,
    1798881619586568211962789888, 1798881619586568211962789888, 2727336649050603418137133056, 86016527806908646002805178368, 44101613899541672293281300480, 1798881619586568211962789888,
    324154509886159763190832955392, 36325803027780377441571176448, 86016508921714378770785239040, 36383831467121879641957072896, 32611982909924236616873803776, 44101613899541672293281300480,
    1798881619586568211962789888, 324244943555628020228220256256, 86688911095367321662145953792, 324154509886159763190832955392, 87540472108091951540948959232, 541668157640453156835136897024,
    36325803027780377441571176448, 36325803027780377441571176448, 67487074954167059048797569024, 2147052255635581414278168576, 86042958716452615741293723648, 25573987576907119160576704512,
    86016508921714378770785239040, 25825205529528996559010660352, 541668379591677851708461940736, 2205080694977083614664065024
  ]
def negativeScales : Array ℕ := #[
    21, 7, 25, 11, 6, 26,
    5, 5, 10, 6, 11, 10,
    17, 6, 6, 7, 42, 8,
    6, 47, 9, 45, 10, 9,
    8, 6, 42, 31, 42, 30,
    31, 32, 31, 8, 8, 21,
    6, 6, 7, 42, 8, 6,
    47, 9, 45, 10, 9, 8,
    6, 47, 32, 47, 31, 25,
    9, 9, 11, 6, 45, 31,
    45, 30, 26, 5
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    21850829698854341, 7139551352398794, 25773324035521374, 11768597882530236, 6794415866926375, 26773324626672734,
    5832890015409720, 5832890015409720, 10913637433615165, 6714245517766967, 11768597882530236, 10913637433615165,
    17850815585727886, 6794415866926375, 6714245517766967, 7139551352398794, 42119044108491408, 8154818109052105,
    6539158811108986, 47032998828248726, 9874981350423323, 45119043791697345, 10877284136413052, 9719388821055554,
    8154818109052105, 6539158811108986, 42119044108491408, 31368663784531846, 42118600552638625, 30382766487650030,
    31368663784531846, 32129834118218590, 31368663784531846, 8154818109052105, 8154818109052105, 21850829698854341,
    6539158811108986, 6539158811108986, 7139551352398794, 42118600552638625, 8154818109052105, 6539158811108986,
    47032596396671633, 9874981350423323, 45118600235890439, 10877284136413052, 9719388821055554, 8154818109052105,
    6539158811108986, 47032998828248726, 32129834118218590, 47032596396671633, 31143936821336773, 25773324035521374,
    9874981350423323, 9874981350423323, 11768597882530236, 6794415866926375, 45119043791697345, 31368663784531846,
    45118600235890439, 30382766487650030, 26773324626672734, 5832890015409720
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
noncomputable def negativeCeiling : ℝ := 205311761 / 100000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 17861373691592479004245884928, coefficient := (-17861373691592479004245884928) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 541668157640453156835136897024, coefficient := (-541668157640453156835136897024) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 541668379591677851708461940736, coefficient := (-541668379591677851708461940736) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 17861198964032612827372978176, coefficient := (-17861198964032612827372978176) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 86042977610190211466435493888, coefficient := (-86042977610190211466435493888) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 324244943555628020228220256256, coefficient := (-324244943555628020228220256256) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 86042958716452615741293723648, coefficient := (-86042958716452615741293723648) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 86042977610190211466435493888, coefficient := (-86042977610190211466435493888) }, { argument := 25573987576907119160576704512, coefficient := (-25573987576907119160576704512) }, { argument := 86016527806908646002805178368, coefficient := (-86016527806908646002805178368) }, { argument := 25825205529528996559010660352, coefficient := (-25825205529528996559010660352) }, { argument := 25573987576907119160576704512, coefficient := (-25573987576907119160576704512) }, { argument := 86688911095367321662145953792, coefficient := (-86688911095367321662145953792) }, { argument := 25573987576907119160576704512, coefficient := (-25573987576907119160576704512) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 17861373691592479004245884928, coefficient := (-17861373691592479004245884928) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 86016527806908646002805178368, coefficient := (-86016527806908646002805178368) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 324154509886159763190832955392, coefficient := (-324154509886159763190832955392) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 86016508921714378770785239040, coefficient := (-86016508921714378770785239040) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 324244943555628020228220256256, coefficient := (-324244943555628020228220256256) }, { argument := 86688911095367321662145953792, coefficient := (-86688911095367321662145953792) }, { argument := 324154509886159763190832955392, coefficient := (-324154509886159763190832955392) }, { argument := 87540472108091951540948959232, coefficient := (-87540472108091951540948959232) }, { argument := 541668157640453156835136897024, coefficient := (-541668157640453156835136897024) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 36325803027780377441571176448, coefficient := (-36325803027780377441571176448) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 86042958716452615741293723648, coefficient := (-86042958716452615741293723648) }, { argument := 25573987576907119160576704512, coefficient := (-25573987576907119160576704512) }, { argument := 86016508921714378770785239040, coefficient := (-86016508921714378770785239040) }, { argument := 25825205529528996559010660352, coefficient := (-25825205529528996559010660352) }, { argument := 541668379591677851708461940736, coefficient := (-541668379591677851708461940736) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }] }

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
def constantNumerator : ℤ := 366959037009676605252822749937664
def positiveArguments : Array ℕ := #[
    19, 17, 18355561, 3563, 18351767, 1799,
    11829805, 285, 93, 5443701, 939, 11829803,
    1881, 843, 285, 93, 3782293, 141,
    57351347, 3489, 111, 114702741, 57, 57,
    1929, 105, 3489, 1929, 236391, 111,
    105, 141
  ]
def positiveCoefficients : Array ℕ := #[
    6021340351084089657109340225536, 2693757525484987478180494311424, 1386906976650707644293679415296, 275673772498363119966598725632, 1386620310115731525350627213312, 278381766334299889317940559872,
    446917397047069946377656074240, 176406455598166689173125201920, 7195526478346272847851159552, 1645257673290494113244296249344, 145303212111121509766284705792, 446917321489206220463332655104,
    145535325868487518567828291584, 130447931639696946467495215104, 176406455598166689173125201920, 7195526478346272847851159552, 35722747383184958008491769856, 5454673298101206836274266112,
    1083336315280906313670273794048, 134974149908334118097595138048, 4294104511271162828556337152, 1083336759183355703416923881472, 4410161389954167229328130048, 4410161389954167229328130048,
    74624572993171829696262832128, 4061990753905154027012751360, 134974149908334118097595138048, 74624572993171829696262832128, 35722397928065225654745956352, 4294104511271162828556337152,
    4061990753905154027012751360, 5454673298101206836274266112
  ]
def positiveScales : Array ℕ := #[
    4, 4, 24, 11, 24, 10,
    23, 8, 6, 22, 9, 23,
    10, 9, 8, 6, 21, 7,
    25, 11, 6, 26, 5, 5,
    10, 6, 11, 10, 17, 6,
    6, 7
  ]
def negativeArguments : Array ℕ := #[
    1399987197, 2372789251, 1399987197, 1881, 1881, 57,
    843, 843, 1929, 105, 285, 285,
    3489, 1929, 236391, 93, 93, 111,
    105, 141, 17, 21, 21, 17
  ]
def negativeCoefficients : Array ℕ := #[
    25825205529528996559010660352, 87540472108091951540948959232, 25825205529528996559010660352, 36383831467121879641957072896, 36383831467121879641957072896, 2205080694977083614664065024,
    32611982909924236616873803776, 32611982909924236616873803776, 37312286496585914848131416064, 2030995376952577013506375680, 44101613899541672293281300480, 44101613899541672293281300480,
    67487074954167059048797569024, 37312286496585914848131416064, 17861198964032612827372978176, 1798881619586568211962789888, 1798881619586568211962789888, 2147052255635581414278168576,
    2030995376952577013506375680, 2727336649050603418137133056, 2693757525484987478180494311424, 3327582825599102178928845914112, 3327582825599102178928845914112, 2693757525484987478180494311424
  ]
def negativeScales : Array ℕ := #[
    30, 31, 30, 10, 10, 5,
    9, 9, 10, 6, 8, 8,
    11, 10, 17, 6, 6, 6,
    6, 7, 4, 4, 4, 4
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[
    4247927513443585, 4087462841250339, 24129713872331901, 11798876768094178, 24129415643868929, 10812979471199464,
    23495922957005738, 8154818109052103, 6539158811107971, 22376156397065497, 9874981347482478, 23495922713097210,
    10877284133344468, 9719388820935039, 8154818109052103, 6539158811107971, 21850829696985677, 7139551352398793,
    25773324035127069, 11768597882173550, 6794415866314396, 26773324626278425, 5832890014087662, 5832890014087662,
    10913637427705176, 6714245517659862, 11768597882173550, 10913637427705176, 17850815583859725, 6794415866314396,
    6714245517659862, 7139551352398793
  ]
def negativeLogUpperNumerators : Array ℕ := #[
    30382766487650030, 31143936821336773, 30382766487650030, 10877284136413052, 10877284136413052, 5832890015409720,
    9719388821055554, 9719388821055554, 10913637433615165, 6714245517766967, 8154818109052105, 8154818109052105,
    11768597882530236, 10913637433615165, 17850815585727886, 6539158811108986, 6539158811108986, 6794415866926375,
    6714245517766967, 7139551352398794, 4087462841250340, 4392317422778766, 4392317422778766, 4087462841250340
  ]

abbrev PositiveTerm := Fin 32
abbrev NegativeTerm := Fin 24
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
noncomputable def positiveFloor : ℝ := 2867716883 / 1000000000000
noncomputable def negativeCeiling : ℝ := 143766939 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 25825205529528996559010660352, coefficient := (-25825205529528996559010660352) }, { argument := 87540472108091951540948959232, coefficient := (-87540472108091951540948959232) }, { argument := 25825205529528996559010660352, coefficient := (-25825205529528996559010660352) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 36383831467121879641957072896, coefficient := (-36383831467121879641957072896) }, { argument := 2205080694977083614664065024, coefficient := (-2205080694977083614664065024) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 32611982909924236616873803776, coefficient := (-32611982909924236616873803776) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 44101613899541672293281300480, coefficient := (-44101613899541672293281300480) }, { argument := 67487074954167059048797569024, coefficient := (-67487074954167059048797569024) }, { argument := 37312286496585914848131416064, coefficient := (-37312286496585914848131416064) }, { argument := 17861198964032612827372978176, coefficient := (-17861198964032612827372978176) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 1798881619586568211962789888, coefficient := (-1798881619586568211962789888) }, { argument := 2147052255635581414278168576, coefficient := (-2147052255635581414278168576) }, { argument := 2030995376952577013506375680, coefficient := (-2030995376952577013506375680) }, { argument := 2727336649050603418137133056, coefficient := (-2727336649050603418137133056) }, { argument := 6021340351084089657109340225536, coefficient := 6021340351084089657109340225536 }, { argument := 2693757525484987478180494311424, coefficient := 2693757525484987478180494311424 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }, { argument := 1386906976650707644293679415296, coefficient := 1386906976650707644293679415296 }, { argument := 275673772498363119966598725632, coefficient := 275673772498363119966598725632 }, { argument := 1386620310115731525350627213312, coefficient := 1386620310115731525350627213312 }, { argument := 278381766334299889317940559872, coefficient := 278381766334299889317940559872 }, { argument := 3327582825599102178928845914112, coefficient := (-3327582825599102178928845914112) }, { argument := 446917397047069946377656074240, coefficient := 446917397047069946377656074240 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 1645257673290494113244296249344, coefficient := 1645257673290494113244296249344 }, { argument := 145303212111121509766284705792, coefficient := 145303212111121509766284705792 }, { argument := 446917321489206220463332655104, coefficient := 446917321489206220463332655104 }, { argument := 145535325868487518567828291584, coefficient := 145535325868487518567828291584 }, { argument := 130447931639696946467495215104, coefficient := 130447931639696946467495215104 }, { argument := 176406455598166689173125201920, coefficient := 176406455598166689173125201920 }, { argument := 7195526478346272847851159552, coefficient := 7195526478346272847851159552 }, { argument := 3327582825599102178928845914112, coefficient := (-3327582825599102178928845914112) }, { argument := 35722747383184958008491769856, coefficient := 35722747383184958008491769856 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 1083336315280906313670273794048, coefficient := 1083336315280906313670273794048 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 1083336759183355703416923881472, coefficient := 1083336759183355703416923881472 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 4410161389954167229328130048, coefficient := 4410161389954167229328130048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 134974149908334118097595138048, coefficient := 134974149908334118097595138048 }, { argument := 74624572993171829696262832128, coefficient := 74624572993171829696262832128 }, { argument := 35722397928065225654745956352, coefficient := 35722397928065225654745956352 }, { argument := 4294104511271162828556337152, coefficient := 4294104511271162828556337152 }, { argument := 4061990753905154027012751360, coefficient := 4061990753905154027012751360 }, { argument := 5454673298101206836274266112, coefficient := 5454673298101206836274266112 }, { argument := 2693757525484987478180494311424, coefficient := (-2693757525484987478180494311424) }] }

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

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch2.Chunk5
