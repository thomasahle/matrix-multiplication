import MatrixMultiplication.SignedDyadicLogCertificate
import MatrixMultiplication.RationalDyadicLog

/-! Line-budgeted numeric term shards, part 2, for level-four region 1, branch 1,
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

namespace TermShard4

/-! Directed signed-log shard 4.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-1700461786167975194717849145835520)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    1572824813, 159539531, 24927, 734835, 647761, 45529,
    25425, 45529, 1291197, 82343, 25425, 20253807,
    1296545, 734835, 1291197, 45529, 1296545, 45529,
    1291197, 2581, 24927, 2478135, 73086513, 64419197,
    4537091, 10115973, 4537091, 128419215, 65473301, 10115973,
    2013244047, 128875333, 73086513, 128419215, 4537091, 128875333,
    4537091, 128419215, 32838367, 2478135, 17092736547, 337018185177,
    674036159923, 2136597775, 158631, 4678485, 4123653, 290447,
    647555, 290447, 8220491, 4191067, 647555, 128871791,
    8249565, 4678485, 8220491, 290447, 8249565, 290447,
    8220491, 2102049, 158631, 30462839283
  ]
def negativeCoefficients : Array ℕ := #[
    232107974385528669893992382464, 5885969795993302590073864192, 941715434547933169934401536, 13880640697758062962425200640, 24471718682480994026151477248, 860018494394288307737460736,
    15368469481850973383452262400, 860018494394288307737460736, 24390021742327349163954536448, 24886644691131852533207662592, 15368469481850973383452262400, 382583597309242401266690162688,
    24491042606128896614365921280, 13880640697758062962425200640, 24390021742327349163954536448, 860018494394288307737460736, 24491042606128896614365921280, 860018494394288307737460736,
    24390021742327349163954536448, 24961900323402863199333122048, 941715434547933169934401536, 23405323328052336483285073920, 345141299341016602216180482048, 608422113532353600682379444224,
    21425806468129521472253198336, 382170654694514348010623729664, 21425806468129521472253198336, 606442596672430785671347568640, 618377844330471249679055060992, 382170654694514348010623729664,
    9507276209389640703475514867712, 608596553027864322506928160768, 345141299341016602216180482048, 606442596672430785671347568640, 21425806468129521472253198336, 608596553027864322506928160768,
    21425806468129521472253198336, 606442596672430785671347568640, 620299214691890490748570697728, 23405323328052336483285073920, 78826334150462728692446527488, 3108444105073086501917363798016,
    3108443134631385958223699771392, 78826544687764527957986508800, 1498227435088189379787620352, 22093520754608392087598530560, 38946801428369722188786302976, 1371597177850039843382362112,
    24463936222517224850839306240, 1371597177850039843382362112, 38820171171131572652381044736, 39583508656522070713658507264, 24463936222517224850839306240, 608579826405781998223581249536,
    38957469254254524717324042240, 22093520754608392087598530560, 38820171171131572652381044736, 1371597177850039843382362112, 38957469254254524717324042240, 1371597177850039843382362112,
    38820171171131572652381044736, 39706582971798619407217852416, 1498227435088189379787620352, 140485050003011694125050232832
  ]
def negativeScales : Array ℕ := #[
    30, 27, 14, 19, 19, 15,
    14, 15, 20, 16, 14, 24,
    20, 19, 20, 15, 20, 15,
    20, 11, 14, 21, 26, 25,
    22, 23, 22, 26, 25, 23,
    30, 26, 26, 26, 22, 26,
    22, 26, 24, 21, 33, 38,
    39, 30, 17, 22, 21, 18,
    19, 18, 22, 21, 19, 26,
    22, 22, 22, 18, 22, 18,
    22, 21, 17, 34
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    30550710841021424, 27249338701029059, 14605421642427233, 19487060817712456, 19305102084279779, 15474498151867701,
    14633960153646315, 15474498151867701, 20300277701061992, 16329358390830435, 14633960153646315, 24271689773384375,
    20306240848905429, 19487060817712456, 20300277701061992, 15474498151867701, 20306240848905429, 15474498151867701,
    20300277701061992, 11333714426093971, 14605421642427233, 21240823351849260, 26123101867609357, 25940987350466467,
    22113336165299392, 23270131755710648, 22113336165299392, 26936285852298571, 25964403395312723, 23270131755710648,
    30906874926392502, 26941400923474493, 26123101867609357, 26936285852298571, 22113336165299392, 26941400923474493,
    22113336165299392, 26936285852298571, 24968879064458825, 21240823351849260, 33992664360897859, 38294035483704729,
    39294035033302020, 30992668214189043, 17275315207496350, 22157609997244880, 21975491522169910, 18147915402909608,
    19304643207556371, 18147915402909608, 22970793150983731, 21998886177711138, 19304643207556371, 26941361272001058,
    22975886633336321, 22157609997244880, 22970793150983731, 18147915402909608, 22975886633336321, 18147915402909608,
    22970793150983731, 21003364869087187, 17275315207496350, 34826331364170652
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
noncomputable def negativeCeiling : ℝ := 9143533767 / 1000000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 232107974385528669893992382464, coefficient := (-232107974385528669893992382464) }, { argument := 5885969795993302590073864192, coefficient := (-5885969795993302590073864192) }, { argument := 941715434547933169934401536, coefficient := (-941715434547933169934401536) }, { argument := 13880640697758062962425200640, coefficient := (-13880640697758062962425200640) }, { argument := 24471718682480994026151477248, coefficient := (-24471718682480994026151477248) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 15368469481850973383452262400, coefficient := (-15368469481850973383452262400) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 24886644691131852533207662592, coefficient := (-24886644691131852533207662592) }, { argument := 15368469481850973383452262400, coefficient := (-15368469481850973383452262400) }, { argument := 382583597309242401266690162688, coefficient := (-382583597309242401266690162688) }, { argument := 24491042606128896614365921280, coefficient := (-24491042606128896614365921280) }, { argument := 13880640697758062962425200640, coefficient := (-13880640697758062962425200640) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24491042606128896614365921280, coefficient := (-24491042606128896614365921280) }, { argument := 860018494394288307737460736, coefficient := (-860018494394288307737460736) }, { argument := 24390021742327349163954536448, coefficient := (-24390021742327349163954536448) }, { argument := 24961900323402863199333122048, coefficient := (-24961900323402863199333122048) }, { argument := 941715434547933169934401536, coefficient := (-941715434547933169934401536) }, { argument := 23405323328052336483285073920, coefficient := (-23405323328052336483285073920) }, { argument := 345141299341016602216180482048, coefficient := (-345141299341016602216180482048) }, { argument := 608422113532353600682379444224, coefficient := (-608422113532353600682379444224) }, { argument := 21425806468129521472253198336, coefficient := (-21425806468129521472253198336) }, { argument := 382170654694514348010623729664, coefficient := (-382170654694514348010623729664) }, { argument := 21425806468129521472253198336, coefficient := (-21425806468129521472253198336) }, { argument := 606442596672430785671347568640, coefficient := (-606442596672430785671347568640) }, { argument := 618377844330471249679055060992, coefficient := (-618377844330471249679055060992) }, { argument := 382170654694514348010623729664, coefficient := (-382170654694514348010623729664) }, { argument := 9507276209389640703475514867712, coefficient := (-9507276209389640703475514867712) }, { argument := 608596553027864322506928160768, coefficient := (-608596553027864322506928160768) }, { argument := 345141299341016602216180482048, coefficient := (-345141299341016602216180482048) }, { argument := 606442596672430785671347568640, coefficient := (-606442596672430785671347568640) }, { argument := 21425806468129521472253198336, coefficient := (-21425806468129521472253198336) }, { argument := 608596553027864322506928160768, coefficient := (-608596553027864322506928160768) }, { argument := 21425806468129521472253198336, coefficient := (-21425806468129521472253198336) }, { argument := 606442596672430785671347568640, coefficient := (-606442596672430785671347568640) }, { argument := 620299214691890490748570697728, coefficient := (-620299214691890490748570697728) }, { argument := 23405323328052336483285073920, coefficient := (-23405323328052336483285073920) }, { argument := 78826334150462728692446527488, coefficient := (-78826334150462728692446527488) }, { argument := 3108444105073086501917363798016, coefficient := (-3108444105073086501917363798016) }, { argument := 3108443134631385958223699771392, coefficient := (-3108443134631385958223699771392) }, { argument := 78826544687764527957986508800, coefficient := (-78826544687764527957986508800) }, { argument := 1498227435088189379787620352, coefficient := (-1498227435088189379787620352) }, { argument := 22093520754608392087598530560, coefficient := (-22093520754608392087598530560) }, { argument := 38946801428369722188786302976, coefficient := (-38946801428369722188786302976) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 24463936222517224850839306240, coefficient := (-24463936222517224850839306240) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 39583508656522070713658507264, coefficient := (-39583508656522070713658507264) }, { argument := 24463936222517224850839306240, coefficient := (-24463936222517224850839306240) }, { argument := 608579826405781998223581249536, coefficient := (-608579826405781998223581249536) }, { argument := 38957469254254524717324042240, coefficient := (-38957469254254524717324042240) }, { argument := 22093520754608392087598530560, coefficient := (-22093520754608392087598530560) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38957469254254524717324042240, coefficient := (-38957469254254524717324042240) }, { argument := 1371597177850039843382362112, coefficient := (-1371597177850039843382362112) }, { argument := 38820171171131572652381044736, coefficient := (-38820171171131572652381044736) }, { argument := 39706582971798619407217852416, coefficient := (-39706582971798619407217852416) }, { argument := 1498227435088189379787620352, coefficient := (-1498227435088189379787620352) }, { argument := 140485050003011694125050232832, coefficient := (-140485050003011694125050232832) }] }

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

end TermShard4


end Parent0

namespace Parent0

namespace TermShard5

/-! Directed signed-log shard 5.  The untrusted producer supplies only integer arrays and
rational endpoints; the generic checker proves the direction of every logarithm bound. -/

def bits : ℕ := 116
def constantNumerator : ℤ := (-8924590717919887709055786749526016)
def positiveArguments : Array ℕ := #[]
def positiveCoefficients : Array ℕ := #[]
def positiveScales : Array ℕ := #[]
def negativeArguments : Array ℕ := #[
    600513452481, 1201026528779, 237991577, 96358418357, 346002561839, 24093050695,
    41541994831557, 3947978490077499, 1976858073, 5115087291, 2140691859, 122032028889,
    986946256015599, 2140691859, 3964723479, 2006004705, 1976858073, 3906430215,
    122032028889, 3906430215, 10385444418321, 5115087291, 13580306393149, 626816183250685,
    73119, 25640202304665865, 367365, 82251, 2332023, 2379297,
    367365, 18288759, 585375, 2507268796398217, 2332023, 82251,
    585375, 82251, 2332023, 1193259, 13580306393149, 1966893114077963,
    76977530681080357, 76977543499844853, 1966906046383579, 39549, 2331939, 513895,
    144529, 645483, 144529, 4097493, 4180463, 645483,
    32133747, 257129, 2331939, 4097493, 144529, 257129,
    144529, 4097493, 2096581, 39549
  ]
def negativeCoefficients : Array ℕ := #[
    5538758985368374592875316379648, 5538757250530493122805252489216, 140485430803761293729751629824, 222187385347376927440176676864, 797827588386486988392500297728, 222219170062787521895003586560,
    11693032027726698496646971392, 1111257153548734871009539129344, 4558324367834704271162474496, 5897294135735080918519382016, 78977589727293066149822988288, 140693350356932096762434289664,
    1111202697706639450662582091776, 78977589727293066149822988288, 4571014958758772869907349504, 4625531925474028418142044160, 4558324367834704271162474496, 4503807401119448722927779840,
    140693350356932096762434289664, 4503807401119448722927779840, 11692970903106863295369314304, 5897294135735080918519382016, 30580131405881500476429565952, 5645858258635163004248281579520,
    22098861751100517656335220736, 57736602772498661183350919659520, 13878657303835257711435448320, 776838731165022376943419392, 22025334504962237280357974016, 22471824811184596496022503424,
    13878657303835257711435448320, 345464890059522278915158573056, 22114842239278548535738368000, 5645867408588341042327706402816, 22025334504962237280357974016, 776838731165022376943419392,
    22114842239278548535738368000, 776838731165022376943419392, 22025334504962237280357974016, 22540025227930199912198701056, 30580131405881500476429565952, 1107262386954888580864153747456,
    43334497311401802368680548368384, 43334504527724678310648543707136, 1107269667195732738235745435648, 1494118976248092788451704832, 22024541147393115179962073088, 38828808379428741233476894720,
    1365037810805333906180538368, 24385658275697177611777081344, 1365037810805333906180538368, 38699727213985982351205728256, 39483356708153371277966442496, 24385658275697177611777081344,
    606989319207252053106672795648, 38856235883961248132878041088, 22024541147393115179962073088, 38699727213985982351205728256, 1365037810805333906180538368, 38856235883961248132878041088,
    1365037810805333906180538368, 38699727213985982351205728256, 39603295372085294527103893504, 1494118976248092788451704832
  ]
def negativeScales : Array ℕ := #[
    39, 40, 27, 36, 38, 34,
    45, 51, 30, 32, 30, 36,
    49, 30, 31, 30, 30, 31,
    36, 31, 43, 32, 43, 49,
    16, 54, 18, 16, 21, 21,
    18, 24, 19, 51, 21, 16,
    19, 16, 21, 20, 43, 50,
    56, 56, 50, 15, 21, 18,
    17, 19, 17, 21, 21, 19,
    24, 17, 21, 21, 17, 17,
    17, 21, 20, 15
  ]
def logBoundDenominator : ℕ := 1000000000000000
def positiveLogLowerNumerators : Array ℕ := #[]
def negativeLogUpperNumerators : Array ℕ := #[
    39127405608776394, 40127405156898562, 27826335274754877, 36487691662009759, 38331991763526854, 34487898030033898,
    45239635729075396, 51810035553627095, 30880562154663594, 32252111714331890, 30995430018524957, 36828468896419295,
    49809964854330044, 30995430018524957, 31884573105466988, 30901677848221955, 30880562154663594, 31863203698130373,
    36828468896419295, 31863203698130373, 43239628187454352, 32252111714331890, 43626581262974595, 49155035756469226,
    16157958719298466, 54509257163258828, 18486854657413929, 16327745598655941, 21153150586774380, 21182103939314677,
    18486854657413929, 24124453847264900, 19159001607361153, 51155038094569258, 21153150586774380, 16327745598655941,
    19159001607361153, 16327745598655941, 21153150586774380, 20186475787094054, 43626581262974595, 50804839984090369,
    56095286910685879, 56095287150932172, 50804849469767033, 15271353596035632, 21153098619634233, 18971114104607005,
    17140999475525776, 19300019574402030, 17140999475525776, 21966310067699619, 21995231325629272, 19300019574402030,
    24937585890719630, 17972132821569416, 21153098619634233, 21966310067699619, 17140999475525776, 17972132821569416,
    17140999475525776, 21966310067699619, 20999607161668485, 15271353596035632
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
noncomputable def negativeCeiling : ℝ := 56249536823 / 500000000000

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
def rawForm : Form := { constantNumerator := 0, terms := [{ argument := 5538758985368374592875316379648, coefficient := (-5538758985368374592875316379648) }, { argument := 5538757250530493122805252489216, coefficient := (-5538757250530493122805252489216) }, { argument := 140485430803761293729751629824, coefficient := (-140485430803761293729751629824) }, { argument := 222187385347376927440176676864, coefficient := (-222187385347376927440176676864) }, { argument := 797827588386486988392500297728, coefficient := (-797827588386486988392500297728) }, { argument := 222219170062787521895003586560, coefficient := (-222219170062787521895003586560) }, { argument := 11693032027726698496646971392, coefficient := (-11693032027726698496646971392) }, { argument := 1111257153548734871009539129344, coefficient := (-1111257153548734871009539129344) }, { argument := 4558324367834704271162474496, coefficient := (-4558324367834704271162474496) }, { argument := 5897294135735080918519382016, coefficient := (-5897294135735080918519382016) }, { argument := 78977589727293066149822988288, coefficient := (-78977589727293066149822988288) }, { argument := 140693350356932096762434289664, coefficient := (-140693350356932096762434289664) }, { argument := 1111202697706639450662582091776, coefficient := (-1111202697706639450662582091776) }, { argument := 78977589727293066149822988288, coefficient := (-78977589727293066149822988288) }, { argument := 4571014958758772869907349504, coefficient := (-4571014958758772869907349504) }, { argument := 4625531925474028418142044160, coefficient := (-4625531925474028418142044160) }, { argument := 4558324367834704271162474496, coefficient := (-4558324367834704271162474496) }, { argument := 4503807401119448722927779840, coefficient := (-4503807401119448722927779840) }, { argument := 140693350356932096762434289664, coefficient := (-140693350356932096762434289664) }, { argument := 4503807401119448722927779840, coefficient := (-4503807401119448722927779840) }, { argument := 11692970903106863295369314304, coefficient := (-11692970903106863295369314304) }, { argument := 5897294135735080918519382016, coefficient := (-5897294135735080918519382016) }, { argument := 30580131405881500476429565952, coefficient := (-30580131405881500476429565952) }, { argument := 5645858258635163004248281579520, coefficient := (-5645858258635163004248281579520) }, { argument := 22098861751100517656335220736, coefficient := (-22098861751100517656335220736) }, { argument := 57736602772498661183350919659520, coefficient := (-57736602772498661183350919659520) }, { argument := 13878657303835257711435448320, coefficient := (-13878657303835257711435448320) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 22471824811184596496022503424, coefficient := (-22471824811184596496022503424) }, { argument := 13878657303835257711435448320, coefficient := (-13878657303835257711435448320) }, { argument := 345464890059522278915158573056, coefficient := (-345464890059522278915158573056) }, { argument := 22114842239278548535738368000, coefficient := (-22114842239278548535738368000) }, { argument := 5645867408588341042327706402816, coefficient := (-5645867408588341042327706402816) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22114842239278548535738368000, coefficient := (-22114842239278548535738368000) }, { argument := 776838731165022376943419392, coefficient := (-776838731165022376943419392) }, { argument := 22025334504962237280357974016, coefficient := (-22025334504962237280357974016) }, { argument := 22540025227930199912198701056, coefficient := (-22540025227930199912198701056) }, { argument := 30580131405881500476429565952, coefficient := (-30580131405881500476429565952) }, { argument := 1107262386954888580864153747456, coefficient := (-1107262386954888580864153747456) }, { argument := 43334497311401802368680548368384, coefficient := (-43334497311401802368680548368384) }, { argument := 43334504527724678310648543707136, coefficient := (-43334504527724678310648543707136) }, { argument := 1107269667195732738235745435648, coefficient := (-1107269667195732738235745435648) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38828808379428741233476894720, coefficient := (-38828808379428741233476894720) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39483356708153371277966442496, coefficient := (-39483356708153371277966442496) }, { argument := 24385658275697177611777081344, coefficient := (-24385658275697177611777081344) }, { argument := 606989319207252053106672795648, coefficient := (-606989319207252053106672795648) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 22024541147393115179962073088, coefficient := (-22024541147393115179962073088) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38856235883961248132878041088, coefficient := (-38856235883961248132878041088) }, { argument := 1365037810805333906180538368, coefficient := (-1365037810805333906180538368) }, { argument := 38699727213985982351205728256, coefficient := (-38699727213985982351205728256) }, { argument := 39603295372085294527103893504, coefficient := (-39603295372085294527103893504) }, { argument := 1494118976248092788451704832, coefficient := (-1494118976248092788451704832) }] }

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

end TermShard5


end Parent0

end MatrixMultiplication.Generated.TotalQuotientExponentLevelFourAnalytic.Region1.Branch1.Chunk11
