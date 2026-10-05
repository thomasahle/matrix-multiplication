import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 0, for level-four region 1, branch 1,
parent chunk 10, parent 3; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent3

namespace TermShard0

/-! Directed signed-log shard 0.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-2558879569698982317580069346738176)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    513, 2049, 1021, 2049, 4079941787425, 104966655405,
    154717264314919, 173921015181, 8581546263, 86847261369, 176135607981, 511981871863,
    104966655405, 8581546263, 472701385624497, 38754730870928463, 25891661285, 2097997989,
    449642656643, 810453235435, 4844268494223281, 449642656643, 13223396195, 13259074931,
    25891661285, 25820303813, 810453235435, 25820303813, 59087467794511, 2097997989,
    7501780263357, 637041934358613, 7806577669, 25996484354087347, 304349643, 510566653,
    15516070257, 505983613, 304349643, 248108407515, 15891839957, 2548171629719045,
    15516070257, 510566653, 15891839957, 510566653, 15516070257, 506114557,
    7501780263357, 3465, 51975, 91245, 3465, 28875,
    3465, 91245, 181335, 28875, 2798565, 179025,
    51975, 91245, 3465, 179025
  ]
def negativeCoefficients : Array ℕ := #[
    39691452509587505063953170432, 39633424070246002863567273984, 39498024378449164396000182272, 39633424070246002863567273984, 36748848627081090805897625600, 242036628566162053066716610560,
    1393569227832903492989666459648, 200517278505228794349439942656, 9893849229391224951105650688, 200256150497063153823318540288, 203070530168296284493191315456, 36892181877482493291180064768,
    242036628566162053066716610560, 9893849229391224951105650688, 133053611509750113989434540032, 10908486969322330242452425801728, 59702106170946097988837048320, 77402463940480614120919400448,
    1036805376464534875072821723136, 1868777927222414778706291589120, 10908322892733301033175967858688, 1036805376464534875072821723136, 60982151348607421093542625280, 61146690476573783001739034624,
    59702106170946097988837048320, 59537567042979736080640638976, 1868777927222414778706291589120, 59537567042979736080640638976, 133053148970812961357696073728, 77402463940480614120919400448,
    8446253699667481637072928768, 1434490909098414739774739841024, 36001485087894768909367115776, 14634719656251338167733939339264, 22457039893383470880078692352, 1177286547557683882838982656,
    35777622132571973685727985664, 37335000858007588957094674432, 22457039893383470880078692352, 572099036995605078761306849280, 36644088068391300697962840064, 1434493100259845071615075287040,
    35777622132571973685727985664, 1177286547557683882838982656, 36644088068391300697962840064, 1177286547557683882838982656, 35777622132571973685727985664, 37344662819831540251201896448,
    8446253699667481637072928768, 65451999452573282661826560, 981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560, 1090866657542888044363776000,
    65451999452573282661826560, 1723569318917763110094766080, 1712660652342334229651128320, 1090866657542888044363776000, 26431699112264177314934292480, 1690843319191476468763852800,
    981779991788599239927398400, 1723569318917763110094766080, 65451999452573282661826560, 1690843319191476468763852800
  ]
def negativeScales : Array ℕ := #[
    9, 11, 9, 11, 41, 36,
    47, 37, 32, 36, 37, 38,
    36, 32, 48, 55, 34, 30,
    38, 39, 52, 38, 33, 33,
    34, 34, 39, 34, 45, 30,
    42, 49, 32, 54, 28, 28,
    33, 28, 28, 37, 33, 51,
    33, 28, 33, 28, 33, 28,
    42, 11, 15, 16, 11, 14,
    11, 16, 17, 14, 21, 17,
    15, 16, 11, 17
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    9002815015607055, 11000704269011247, 9995767173005471, 11000704269011247, 41891685710391202, 36611140145736913,
    47136627519080865, 37339641310307843, 32998590499799513, 36337761304756245, 37357895640974223, 38897301776435649,
    36611140145736913, 32998590499799513, 48747922422297203, 55105221952131181, 34591768484635217, 30966366162737762,
    38709987951315395, 39559937985887508, 52105200252122535, 38709987951315395, 33622373703977213, 33626261072826273,
    34591768484635217, 34587786925004147, 39559937985887508, 34587786925004147, 45747917406997082, 30966366162737762,
    42770370144250825, 49178381671862204, 32862043079042322, 54529166051149701, 28181154432644440, 28927524079257861,
    33853044164250811, 28914515426694144, 28181154432644440, 37852179669449421, 33887567121930375, 51178383875553629,
    33853044164250811, 28927524079257861, 33887567121930375, 28927524079257861, 33853044164250811, 28914888734906639,
    42770370144250825, 11758639637295877, 15665530232664571, 16477457884480649, 11758639637295877, 14817533326997925,
    11758639637295877, 16477457884480649, 17468297885195138, 14817533326997925, 21416255825754780, 17449801541577704,
    15665530232664571, 16477457884480649, 11758639637295877, 17449801541577704
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
noncomputable def negativeCeiling : ℝ := 756634131 / 25000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 39691452509587505063953170432, coefficient := (-39691452509587505063953170432) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 39498024378449164396000182272, coefficient := (-39498024378449164396000182272) }, { argument := 39633424070246002863567273984, coefficient := (-39633424070246002863567273984) }, { argument := 36748848627081090805897625600, coefficient := (-36748848627081090805897625600) }, { argument := 242036628566162053066716610560, coefficient := (-242036628566162053066716610560) }, { argument := 1393569227832903492989666459648, coefficient := (-1393569227832903492989666459648) }, { argument := 200517278505228794349439942656, coefficient := (-200517278505228794349439942656) }, { argument := 9893849229391224951105650688, coefficient := (-9893849229391224951105650688) }, { argument := 200256150497063153823318540288, coefficient := (-200256150497063153823318540288) }, { argument := 203070530168296284493191315456, coefficient := (-203070530168296284493191315456) }, { argument := 36892181877482493291180064768, coefficient := (-36892181877482493291180064768) }, { argument := 242036628566162053066716610560, coefficient := (-242036628566162053066716610560) }, { argument := 9893849229391224951105650688, coefficient := (-9893849229391224951105650688) }, { argument := 133053611509750113989434540032, coefficient := (-133053611509750113989434540032) }, { argument := 10908486969322330242452425801728, coefficient := (-10908486969322330242452425801728) }, { argument := 59702106170946097988837048320, coefficient := (-59702106170946097988837048320) }, { argument := 77402463940480614120919400448, coefficient := (-77402463940480614120919400448) }, { argument := 1036805376464534875072821723136, coefficient := (-1036805376464534875072821723136) }, { argument := 1868777927222414778706291589120, coefficient := (-1868777927222414778706291589120) }, { argument := 10908322892733301033175967858688, coefficient := (-10908322892733301033175967858688) }, { argument := 1036805376464534875072821723136, coefficient := (-1036805376464534875072821723136) }, { argument := 60982151348607421093542625280, coefficient := (-60982151348607421093542625280) }, { argument := 61146690476573783001739034624, coefficient := (-61146690476573783001739034624) }, { argument := 59702106170946097988837048320, coefficient := (-59702106170946097988837048320) }, { argument := 59537567042979736080640638976, coefficient := (-59537567042979736080640638976) }, { argument := 1868777927222414778706291589120, coefficient := (-1868777927222414778706291589120) }, { argument := 59537567042979736080640638976, coefficient := (-59537567042979736080640638976) }, { argument := 133053148970812961357696073728, coefficient := (-133053148970812961357696073728) }, { argument := 77402463940480614120919400448, coefficient := (-77402463940480614120919400448) }, { argument := 8446253699667481637072928768, coefficient := (-8446253699667481637072928768) }, { argument := 1434490909098414739774739841024, coefficient := (-1434490909098414739774739841024) }, { argument := 36001485087894768909367115776, coefficient := (-36001485087894768909367115776) }, { argument := 14634719656251338167733939339264, coefficient := (-14634719656251338167733939339264) }, { argument := 22457039893383470880078692352, coefficient := (-22457039893383470880078692352) }, { argument := 1177286547557683882838982656, coefficient := (-1177286547557683882838982656) }, { argument := 35777622132571973685727985664, coefficient := (-35777622132571973685727985664) }, { argument := 37335000858007588957094674432, coefficient := (-37335000858007588957094674432) }, { argument := 22457039893383470880078692352, coefficient := (-22457039893383470880078692352) }, { argument := 572099036995605078761306849280, coefficient := (-572099036995605078761306849280) }, { argument := 36644088068391300697962840064, coefficient := (-36644088068391300697962840064) }, { argument := 1434493100259845071615075287040, coefficient := (-1434493100259845071615075287040) }, { argument := 35777622132571973685727985664, coefficient := (-35777622132571973685727985664) }, { argument := 1177286547557683882838982656, coefficient := (-1177286547557683882838982656) }, { argument := 36644088068391300697962840064, coefficient := (-36644088068391300697962840064) }, { argument := 1177286547557683882838982656, coefficient := (-1177286547557683882838982656) }, { argument := 35777622132571973685727985664, coefficient := (-35777622132571973685727985664) }, { argument := 37344662819831540251201896448, coefficient := (-37344662819831540251201896448) }, { argument := 8446253699667481637072928768, coefficient := (-8446253699667481637072928768) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1712660652342334229651128320, coefficient := (-1712660652342334229651128320) }, { argument := 1090866657542888044363776000, coefficient := (-1090866657542888044363776000) }, { argument := 26431699112264177314934292480, coefficient := (-26431699112264177314934292480) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }, { argument := 981779991788599239927398400, coefficient := (-981779991788599239927398400) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1690843319191476468763852800, coefficient := (-1690843319191476468763852800) }] }

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


end Parent3

namespace Parent3

namespace TermShard1

/-! Directed signed-log shard 1.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-42364710256841921220400812304367616)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    3465, 91245, 91245, 3465, 1882307024049, 3465,
    146890290686819, 39105, 3465, 73445144169973, 3465, 3465,
    143649, 891, 39105, 143649, 3764630474577, 3465,
    891, 3465, 4079942426847, 104966648403, 154717295181273, 173921004147,
    8581545705, 86847255879, 176135596371, 511981952265, 104966648403, 8581545705,
    1715350495814827, 142154760772737877, 93255700193, 472277691, 1619494736135, 2918923994527,
    17769079656148977, 1619494736135, 47624611391, 47754580487, 93255700193, 92995762001,
    2918923994527, 92995762001, 214418075711503, 472277691, 292706944659681, 49977072647139041,
    145953548191, 510084802014558973, 5686597329, 9479267335, 290013675939, 9477049735,
    5686597329, 4645686186753, 297581275151, 1561785903504931, 290013675939, 9479267335,
    297581275151, 9479267335, 290013675939, 9477113095
  ]
def negativeCoefficients : Array ℕ := #[
    65451999452573282661826560, 1723569318917763110094766080, 1723569318917763110094766080, 65451999452573282661826560, 8477157212103943652905058304, 65451999452573282661826560,
    330767529200750943677408346112, 738672565250469904326328320, 65451999452573282661826560, 330767523916062759534469316608, 65451999452573282661826560, 65451999452573282661826560,
    2713452891590966661208866816, 67322056579789662166450176, 738672565250469904326328320, 2713452891590966661208866816, 8477194201246295357543940096, 65451999452573282661826560,
    67322056579789662166450176, 65451999452573282661826560, 36748854386482452670892212224, 242036612420649302552431558656, 1393569505852304238361303842816, 200517265783892912517490409472,
    9893848586061025380485038080, 200256137837985033240138743808, 203070516782877616007697924096, 36892187671057169128661975040, 242036612420649302552431558656, 9893848586061025380485038080,
    482828240860090652222933696512, 40013007977815269054576760717312, 215033004359357179857769332736, 278783542323183386939193556992, 3734300615775265660622885355520, 6730580487206193615721101000704,
    40012410259074597004958075191296, 3734300615775265660622885355520, 219629754484912413879214014464, 220229131147763260826738229248, 215033004359357179857769332736, 214433627696506332910245117952,
    6730580487206193615721101000704, 214433627696506332910245117952, 482826582937911854894095007744, 278783542323183386939193556992, 329558721724523936426905042944, 56269181437680898293053033283584,
    1346183875064605348961428963328, 574304431070030254544872278065152, 839193644626426522730665869312, 43715404633754946227761315840, 1337452014480617657992904441856, 1398565688282895412875052974080,
    839193644626426522730665869312, 21424446033450057001552117235712, 1372351405959660176174433173504, 56269267304458405394925599326208, 1337452014480617657992904441856, 43715404633754946227761315840,
    1372351405959660176174433173504, 43715404633754946227761315840, 1337452014480617657992904441856, 1398575038568531494772576092160
  ]
def negativeScales : Array ℕ := #[
    11, 16, 16, 11, 40, 11,
    47, 15, 11, 46, 11, 11,
    17, 9, 15, 17, 41, 11,
    9, 11, 41, 36, 47, 37,
    32, 36, 37, 38, 36, 32,
    50, 56, 36, 28, 40, 41,
    53, 40, 35, 35, 36, 36,
    41, 36, 47, 28, 48, 55,
    37, 58, 32, 33, 38, 33,
    32, 42, 38, 50, 38, 33,
    38, 33, 38, 33
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    11758639637295877, 16477457884480649, 16477457884480649, 11758639637295877, 40775639105014731, 11758639637295877,
    47061732366652797, 15255065463144076, 11758639637295877, 46061732343602791, 11758639637295877, 11758639637295877,
    17132188424146355, 9799281622158559, 15255065463144076, 17132188424146355, 41775645400042051, 11758639637295877,
    9799281622158559, 11758639637295877, 41891685936495149, 36611140049499198, 47136627806900919, 37339641218779527,
    32998590405990760, 36337761213557099, 37357895545878801, 38897302002997511, 36611140049499198, 32998590405990760,
    50607424814240260, 56980240046082730, 36440472860716983, 28815060148429601, 40558680917580165, 41408573783833663,
    53980218494777555, 40558680917580165, 35470988269373342, 35474920067968665, 36440472860716983, 36436445920153943,
    41408573783833663, 36436445920153943, 47607419860345665, 28815060148429601, 48056450303439390, 55472115917798990,
    37086718327539415, 58823514730372486, 32404918503885284, 33142128409627728, 38077329977601771, 33141790862990851,
    32404918503885284, 42079028842922940, 38114492793672351, 50472118119350112, 38077329977601771, 33142128409627728,
    38114492793672351, 33142128409627728, 38077329977601771, 33141800508276545
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
noncomputable def negativeCeiling : ℝ := 112358101603 / 200000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 1723569318917763110094766080, coefficient := (-1723569318917763110094766080) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 8477157212103943652905058304, coefficient := (-8477157212103943652905058304) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 330767529200750943677408346112, coefficient := (-330767529200750943677408346112) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 330767523916062759534469316608, coefficient := (-330767523916062759534469316608) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 738672565250469904326328320, coefficient := (-738672565250469904326328320) }, { argument := 2713452891590966661208866816, coefficient := (-2713452891590966661208866816) }, { argument := 8477194201246295357543940096, coefficient := (-8477194201246295357543940096) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 67322056579789662166450176, coefficient := (-67322056579789662166450176) }, { argument := 65451999452573282661826560, coefficient := (-65451999452573282661826560) }, { argument := 36748854386482452670892212224, coefficient := (-36748854386482452670892212224) }, { argument := 242036612420649302552431558656, coefficient := (-242036612420649302552431558656) }, { argument := 1393569505852304238361303842816, coefficient := (-1393569505852304238361303842816) }, { argument := 200517265783892912517490409472, coefficient := (-200517265783892912517490409472) }, { argument := 9893848586061025380485038080, coefficient := (-9893848586061025380485038080) }, { argument := 200256137837985033240138743808, coefficient := (-200256137837985033240138743808) }, { argument := 203070516782877616007697924096, coefficient := (-203070516782877616007697924096) }, { argument := 36892187671057169128661975040, coefficient := (-36892187671057169128661975040) }, { argument := 242036612420649302552431558656, coefficient := (-242036612420649302552431558656) }, { argument := 9893848586061025380485038080, coefficient := (-9893848586061025380485038080) }, { argument := 482828240860090652222933696512, coefficient := (-482828240860090652222933696512) }, { argument := 40013007977815269054576760717312, coefficient := (-40013007977815269054576760717312) }, { argument := 215033004359357179857769332736, coefficient := (-215033004359357179857769332736) }, { argument := 278783542323183386939193556992, coefficient := (-278783542323183386939193556992) }, { argument := 3734300615775265660622885355520, coefficient := (-3734300615775265660622885355520) }, { argument := 6730580487206193615721101000704, coefficient := (-6730580487206193615721101000704) }, { argument := 40012410259074597004958075191296, coefficient := (-40012410259074597004958075191296) }, { argument := 3734300615775265660622885355520, coefficient := (-3734300615775265660622885355520) }, { argument := 219629754484912413879214014464, coefficient := (-219629754484912413879214014464) }, { argument := 220229131147763260826738229248, coefficient := (-220229131147763260826738229248) }, { argument := 215033004359357179857769332736, coefficient := (-215033004359357179857769332736) }, { argument := 214433627696506332910245117952, coefficient := (-214433627696506332910245117952) }, { argument := 6730580487206193615721101000704, coefficient := (-6730580487206193615721101000704) }, { argument := 214433627696506332910245117952, coefficient := (-214433627696506332910245117952) }, { argument := 482826582937911854894095007744, coefficient := (-482826582937911854894095007744) }, { argument := 278783542323183386939193556992, coefficient := (-278783542323183386939193556992) }, { argument := 329558721724523936426905042944, coefficient := (-329558721724523936426905042944) }, { argument := 56269181437680898293053033283584, coefficient := (-56269181437680898293053033283584) }, { argument := 1346183875064605348961428963328, coefficient := (-1346183875064605348961428963328) }, { argument := 574304431070030254544872278065152, coefficient := (-574304431070030254544872278065152) }, { argument := 839193644626426522730665869312, coefficient := (-839193644626426522730665869312) }, { argument := 43715404633754946227761315840, coefficient := (-43715404633754946227761315840) }, { argument := 1337452014480617657992904441856, coefficient := (-1337452014480617657992904441856) }, { argument := 1398565688282895412875052974080, coefficient := (-1398565688282895412875052974080) }, { argument := 839193644626426522730665869312, coefficient := (-839193644626426522730665869312) }, { argument := 21424446033450057001552117235712, coefficient := (-21424446033450057001552117235712) }, { argument := 1372351405959660176174433173504, coefficient := (-1372351405959660176174433173504) }, { argument := 56269267304458405394925599326208, coefficient := (-56269267304458405394925599326208) }, { argument := 1337452014480617657992904441856, coefficient := (-1337452014480617657992904441856) }, { argument := 43715404633754946227761315840, coefficient := (-43715404633754946227761315840) }, { argument := 1372351405959660176174433173504, coefficient := (-1372351405959660176174433173504) }, { argument := 43715404633754946227761315840, coefficient := (-43715404633754946227761315840) }, { argument := 1337452014480617657992904441856, coefficient := (-1337452014480617657992904441856) }, { argument := 1398575038568531494772576092160, coefficient := (-1398575038568531494772576092160) }] }

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


end Parent3

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk10
