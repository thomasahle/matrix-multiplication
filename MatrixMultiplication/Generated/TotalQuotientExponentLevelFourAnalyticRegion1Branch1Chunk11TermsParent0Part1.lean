import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 1, for level-four region 1, branch 1,
parent chunk 11, parent 0; certificate `e7987d7fa66008d497e31c976c68f025d57664a145336d358328375cc5738ca3`. Every proof checks at most
64 signed terms. -/

namespace MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11

open scoped BigOperators

open MatrixMultiplication.DyadicEntropy
open MatrixMultiplication.DyadicLogLinear
open MatrixMultiplication.SignedDyadicLogCertificate
open MatrixMultiplication.SignedDyadicLogForm

set_option maxRecDepth 100000
set_option maxHeartbeats 400000
set_option Elab.async false

namespace Parent0

namespace TermShard2

/-! Directed signed-log shard 2.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-45727707186987372573601154451111936)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    80047642837, 117297195163, 47621908885, 3907559951, 408037095766327, 38627464046556873,
    77983343851, 100886563575, 1351085433271, 601592774951, 9656382579337037, 1351085433271,
    78174972449, 9890026699, 77983343851, 19259525677, 601592774951, 19259525677,
    102008742778547, 100886563575, 134017069950771, 3204995019281769, 18187, 525826592363376081,
    22831, 5085, 144977, 148195, 22831, 1138807,
    9113, 51280006436626131, 144977, 5085, 9113, 5085,
    144977, 74305, 134017069950771, 24927, 734835, 647761,
    45529, 25425, 45529, 1291197, 82343, 25425,
    20253807, 1296545, 734835, 1291197, 45529, 1296545,
    45529, 1291197, 2581, 24927, 1966986913225051, 76981280844569057,
    76981293662414501, 1966999845529119, 1401, 82503
  ]
def negativeCoefficients : Array ℕ := #[
    184577297639731073679123021824, 33808614683372233332487094272, 219617291375777497752839127040, 9010219796096754487606116352, 459408928111642417048267522048, 43490658171585191199119876554752,
    179817348253936056596695089152, 232628577343006645649040998400, 3115390901158390138164312276992, 5548713978056921620531703185408, 43488480986049228860599253860352, 3115390901158390138164312276992,
    180259213716999777851117928448, 182438791398607489453558595584, 179817348253936056596695089152, 177637770572328344994254422016, 5548713978056921620531703185408, 177637770572328344994254422016,
    459406535965997043966449549312, 232628577343006645649040998400, 301779613145788986155448926208, 57736057498246682043855925149696, 1374170867583203800023826432, 592028111357299554004145792876544,
    862530793363174958991147008, 48026467130784291823288320, 1369269051173985108292009984, 1399662201857734144887357440, 862530793363174958991147008, 21511456029029328227494002688,
    1377117624268514458637172736, 57736154469886519993699343007744, 1369269051173985108292009984, 48026467130784291823288320, 1377117624268514458637172736, 48026467130784291823288320,
    1369269051173985108292009984, 1403581766038515950414725120, 301779613145788986155448926208, 941715434547933169934401536, 13880640697758062962425200640, 24471718682480994026151477248,
    860018494394288307737460736, 15368469481850973383452262400, 860018494394288307737460736, 24390021742327349163954536448, 24886644691131852533207662592, 15368469481850973383452262400,
    382583597309242401266690162688, 24491042606128896614365921280, 13880640697758062962425200640, 24390021742327349163954536448, 860018494394288307737460736, 24491042606128896614365921280,
    860018494394288307737460736, 24390021742327349163954536448, 24961900323402863199333122048, 941715434547933169934401536, 1107315191180372729257275686912, 43336608465763088338591399542784,
    43336615681568583999967631245312, 1107322471420345440100971184128, 52928283540002983555104768, 779218803872388678131122176
  ]
def negativeScales : Array ℕ := #[
    36, 36, 35, 31, 48, 55,
    36, 36, 40, 39, 53, 40,
    36, 33, 36, 34, 39, 34,
    46, 36, 46, 51, 14, 58,
    14, 12, 17, 17, 14, 20,
    13, 55, 17, 12, 13, 12,
    17, 16, 46, 14, 19, 19,
    15, 14, 15, 20, 16, 14,
    24, 20, 19, 20, 15, 20,
    15, 20, 11, 14, 50, 56,
    56, 50, 10, 16
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    36220139869198668, 36771377559846781, 35470906399883644, 31863620863898367, 48535693645927848, 55100476483690232,
    36182446966315329, 36553943087834940, 40297256042223455, 39129996284305535, 53100404259136002, 40297256042223455,
    36185987754578809, 33203327269658505, 36182446966315329, 34164853121843869, 39129996284305535, 34164853121843869,
    46535686133784671, 36553943087834940, 46929410106324857, 51509243538138260, 14150619965305846, 58867364719979700,
    14478706430677913, 12312032058744863, 17145464515243274, 17177137247337698, 14478706430677913, 20119091835478221,
    13153710352151716, 55509245961240780, 17145464515243274, 12312032058744863, 13153710352151716, 12312032058744863,
    17145464515243274, 16181171672850345, 46929410106324857, 14605421642427233, 19487060817712456, 19305102084279779,
    15474498151867701, 14633960153646315, 15474498151867701, 20300277701061992, 16329358390830435, 14633960153646315,
    24271689773384375, 20306240848905429, 19487060817712456, 20300277701061992, 15474498151867701, 20306240848905429,
    15474498151867701, 20300277701061992, 11333714426093971, 14605421642427233, 50804908783121038, 56095357193668907,
    56095357433886273, 50804918268344228, 10452241240430869, 16332158959591929
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
noncomputable def negativeCeiling : ℝ := 77567991647 / 125000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 184577297639731073679123021824, coefficient := (-184577297639731073679123021824) }, { argument := 33808614683372233332487094272, coefficient := (-33808614683372233332487094272) }, { argument := 219617291375777497752839127040, coefficient := (-219617291375777497752839127040) }, { argument := 9010219796096754487606116352, coefficient := (-9010219796096754487606116352) }, { argument := 459408928111642417048267522048, coefficient := (-459408928111642417048267522048) }, { argument := 43490658171585191199119876554752, coefficient := (-43490658171585191199119876554752) }, { argument := 179817348253936056596695089152, coefficient := (-179817348253936056596695089152) }, { argument := 232628577343006645649040998400, coefficient := (-232628577343006645649040998400) }, { argument := 3115390901158390138164312276992, coefficient := (-3115390901158390138164312276992) }, { argument := 5548713978056921620531703185408, coefficient := (-5548713978056921620531703185408) }, { argument := 43488480986049228860599253860352, coefficient := (-43488480986049228860599253860352) }, { argument := 3115390901158390138164312276992, coefficient := (-3115390901158390138164312276992) }, { argument := 180259213716999777851117928448, coefficient := (-180259213716999777851117928448) }, { argument := 182438791398607489453558595584, coefficient := (-182438791398607489453558595584) }, { argument := 179817348253936056596695089152, coefficient := (-179817348253936056596695089152) }, { argument := 177637770572328344994254422016, coefficient := (-177637770572328344994254422016) }, { argument := 5548713978056921620531703185408, coefficient := (-5548713978056921620531703185408) }, { argument := 177637770572328344994254422016, coefficient := (-177637770572328344994254422016) }, { argument := 459406535965997043966449549312, coefficient := (-459406535965997043966449549312) }, { argument := 232628577343006645649040998400, coefficient := (-232628577343006645649040998400) }, { argument := 301779613145788986155448926208, coefficient := (-301779613145788986155448926208) }, { argument := 57736057498246682043855925149696, coefficient := (-57736057498246682043855925149696) }, { argument := 1374170867583203800023826432, coefficient := (-1374170867583203800023826432) }, { argument := 592028111357299554004145792876544, coefficient := (-592028111357299554004145792876544) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1399662201857734144887357440, coefficient := (-1399662201857734144887357440) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 21511456029029328227494002688, coefficient := (-21511456029029328227494002688) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 57736154469886519993699343007744, coefficient := (-57736154469886519993699343007744) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1403581766038515950414725120, coefficient := (-1403581766038515950414725120) }, { argument := 301779613145788986155448926208, coefficient := (-301779613145788986155448926208) }, { argument := 941715434547933169934401536, coefficient := (-941715434547933169934401536) }, { argument := 13880640697758062962425200640, coefficient := (-13880640697758062962425200640) }, { argument := 24471718682480994026151477248, coefficient := (-24471718682480994026151477248) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 15368469481850973383452262400, coefficient := (-15368469481850973383452262400) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 24886644691131852533207662592, coefficient := (-24886644691131852533207662592) }, { argument := 15368469481850973383452262400, coefficient := (-15368469481850973383452262400) }, { argument := 382583597309242401266690162688, coefficient := (-382583597309242401266690162688) }, { argument := 24491042606128896614365921280, coefficient := (-24491042606128896614365921280) }, { argument := 13880640697758062962425200640, coefficient := (-13880640697758062962425200640) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24491042606128896614365921280, coefficient := (-24491042606128896614365921280) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 24961900323402863199333122048, coefficient := (-24961900323402863199333122048) }, { argument := 941715434547933169934401536, coefficient := (-941715434547933169934401536) }, { argument := 1107315191180372729257275686912, coefficient := (-1107315191180372729257275686912) }, { argument := 43336608465763088338591399542784, coefficient := (-43336608465763088338591399542784) }, { argument := 43336615681568583999967631245312, coefficient := (-43336615681568583999967631245312) }, { argument := 1107322471420345440100971184128, coefficient := (-1107322471420345440100971184128) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }] }

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


end Parent0

namespace Parent0

namespace TermShard3

/-! Directed signed-log shard 3.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-203323104136035168038563807756288)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    18187, 5085, 22831, 5085, 144977, 148195,
    22831, 1138807, 9113, 82503, 144977, 5085,
    9113, 5085, 144977, 74305, 1401, 986451477,
    19450692159, 38901372181, 123306763, 15004994296919, 55237801395545, 937704412645,
    39549, 2331939, 513895, 144529, 645483, 144529,
    4097493, 4180463, 645483, 32133747, 257129, 2331939,
    4097493, 144529, 257129, 144529, 4097493, 2096581,
    39549, 161163, 4753407, 4189637, 295165, 164483,
    295165, 8352113, 266115, 164483, 130926491, 8381077,
    4753407, 8352113, 295165, 8381077, 295165, 8352113,
    266945, 161163, 159539105, 196603163
  ]
def negativeCoefficients : Array ℕ := #[
    1374170867583203800023826432, 48026467130784291823288320, 862530793363174958991147008, 48026467130784291823288320, 1369269051173985108292009984, 1399662201857734144887357440,
    862530793363174958991147008, 21511456029029328227494002688, 1377117624268514458637172736, 779218803872388678131122176, 1369269051173985108292009984, 48026467130784291823288320,
    1377117624268514458637172736, 48026467130784291823288320, 1369269051173985108292009984, 1403581766038515950414725120, 52928283540002983555104768, 4549204484337946015152734208,
    179400970156791046830368489472, 179400914184757841177161498624, 4549216599237116423900758016, 33788243362150413008122150912, 124384470890870962963779420160, 33784361946973534539858575360,
    1494118976248092788451704832, 22024541147393115179962073088, 38828808379428741233476894720, 1365037810805333906180538368, 24385658275697177611777081344, 1365037810805333906180538368,
    38699727213985982351205728256, 39483356708153371277966442496, 24385658275697177611777081344, 606989319207252053106672795648, 38856235883961248132878041088, 22024541147393115179962073088,
    38699727213985982351205728256, 1365037810805333906180538368, 38856235883961248132878041088, 1365037810805333906180538368, 38699727213985982351205728256, 39603295372085294527103893504,
    1494118976248092788451704832, 1522141498957441263149776896, 22447329896237951646299062272, 39570002688381063528347336704, 1393877302916218829500579840, 24855968198459131317899493376,
    1393877302916218829500579840, 39441738492339841094698139648, 40214161810843380353366753280, 24855968198459131317899493376, 618282872818134258244162420736, 39578517115149677498667630592,
    22447329896237951646299062272, 39441738492339841094698139648, 1393877302916218829500579840, 39578517115149677498667630592, 1393877302916218829500579840, 39441738492339841094698139648,
    40339587864628398130242519040, 1522141498957441263149776896, 5885954079367351789535887360, 232108046844339391425111130112
  ]
def negativeScales : Array ℕ := #[
    14, 12, 14, 12, 17, 17,
    14, 20, 13, 16, 17, 12,
    13, 12, 17, 16, 10, 29,
    34, 35, 26, 43, 45, 39,
    15, 21, 18, 17, 19, 17,
    21, 21, 19, 24, 17, 21,
    21, 17, 17, 17, 21, 20,
    15, 17, 22, 21, 18, 17,
    18, 22, 18, 17, 26, 22,
    22, 22, 18, 22, 18, 22,
    18, 17, 27, 27
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    14150619965305846, 12312032058744863, 14478706430677913, 12312032058744863, 17145464515243274, 17177137247337698,
    14478706430677913, 20119091835478221, 13153710352151716, 16332158959591929, 17145464515243274, 12312032058744863,
    13153710352151716, 12312032058744863, 17145464515243274, 16181171672850345, 10452241240430869, 29877672849336307,
    34179102443755493, 35179101993643170, 26877676691344878, 43770508004483922, 45650721131378060, 39770342265766305,
    15271353596035632, 21153098619634233, 18971114104607005, 17140999475525776, 19300019574402030, 17140999475525776,
    21966310067699619, 21995231325629272, 19300019574402030, 24937585890719630, 17972132821569416, 21153098619634233,
    21966310067699619, 17140999475525776, 17972132821569416, 17140999475525776, 21966310067699619, 20999607161668485,
    15271353596035632, 17298161040613272, 22180530503836938, 21998393843250515, 18171162134452789, 17327578957588370,
    18171162134452789, 22993709821731052, 18021690306915334, 17327578957588370, 26964181806709840, 22998704240106737,
    22180530503836938, 22993709821731052, 18171162134452789, 22998704240106737, 18171162134452789, 22993709821731052,
    18026183001364841, 17298161040613272, 27249334848761824, 27550711291397810
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
noncomputable def negativeCeiling : ℝ := 932659913 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 1374170867583203800023826432, coefficient := (-1374170867583203800023826432) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1399662201857734144887357440, coefficient := (-1399662201857734144887357440) }, { argument := 862530793363174958991147008, coefficient := (-862530793363174958991147008) }, { argument := 21511456029029328227494002688, coefficient := (-21511456029029328227494002688) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 779218803872388678131122176, coefficient := (-779218803872388678131122176) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1377117624268514458637172736, coefficient := (-1377117624268514458637172736) }, { argument := 48026467130784291823288320, coefficient := (-48026467130784291823288320) }, { argument := 1369269051173985108292009984, coefficient := (-1369269051173985108292009984) }, { argument := 1403581766038515950414725120, coefficient := (-1403581766038515950414725120) }, { argument := 52928283540002983555104768, coefficient := (-52928283540002983555104768) }, { argument := 4549204484337946015152734208, coefficient := (-4549204484337946015152734208) }, { argument := 179400970156791046830368489472, coefficient := (-179400970156791046830368489472) }, { argument := 179400914184757841177161498624, coefficient := (-179400914184757841177161498624) }, { argument := 4549216599237116423900758016, coefficient := (-4549216599237116423900758016) }, { argument := 33788243362150413008122150912, coefficient := (-33788243362150413008122150912) }, { argument := 124384470890870962963779420160, coefficient := (-124384470890870962963779420160) }, { argument := 33784361946973534539858575360, coefficient := (-33784361946973534539858575360) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38828808379428741233476894720, coefficient := (-38828808379428741233476894720) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39483356708153371277966442496, coefficient := (-39483356708153371277966442496) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 606989319207252053106672795648, coefficient := (-606989319207252053106672795648) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39603295372085294527103893504, coefficient := (-39603295372085294527103893504) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }, { argument := 1522141498957441263149776896, coefficient := (-1522141498957441263149776896) }, { argument := 22447329896237951646299062272, coefficient := (-22447329896237951646299062272) }, { argument := 39570002688381063528347336704, coefficient := (-39570002688381063528347336704) }, { argument := 1393877302916218829500579840, coefficient := (-1393877302916218829500579840) }, { argument := 24855968198459131317899493376, coefficient := (-24855968198459131317899493376) }, { argument := 1393877302916218829500579840, coefficient := (-1393877302916218829500579840) }, { argument := 39441738492339841094698139648, coefficient := (-39441738492339841094698139648) }, { argument := 40214161810843380353366753280, coefficient := (-40214161810843380353366753280) }, { argument := 24855968198459131317899493376, coefficient := (-24855968198459131317899493376) }, { argument := 618282872818134258244162420736, coefficient := (-618282872818134258244162420736) }, { argument := 39578517115149677498667630592, coefficient := (-39578517115149677498667630592) }, { argument := 22447329896237951646299062272, coefficient := (-22447329896237951646299062272) }, { argument := 39441738492339841094698139648, coefficient := (-39441738492339841094698139648) }, { argument := 1393877302916218829500579840, coefficient := (-1393877302916218829500579840) }, { argument := 39578517115149677498667630592, coefficient := (-39578517115149677498667630592) }, { argument := 1393877302916218829500579840, coefficient := (-1393877302916218829500579840) }, { argument := 39441738492339841094698139648, coefficient := (-39441738492339841094698139648) }, { argument := 40339587864628398130242519040, coefficient := (-40339587864628398130242519040) }, { argument := 1522141498957441263149776896, coefficient := (-1522141498957441263149776896) }, { argument := 5885954079367351789535887360, coefficient := (-5885954079367351789535887360) }, { argument := 232108046844339391425111130112, coefficient := (-232108046844339391425111130112) }] }

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


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
